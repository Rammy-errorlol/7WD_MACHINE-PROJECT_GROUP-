import socket
import threading
import struct
import hashlib
import os
import time
import json
import argparse
from typing import Dict, Tuple, List, Optional, Any, Set

from card_engine import (
    CardDatabaseEngine,
    compute_all_scores,
    parse_card_cost,
    verify_chaining,
    sha256_hex,
    sha256_hash,
    RESOURCE_KEYS
)

MSG_LOBBY_PRESENCE   = 0x01
MSG_LOBBY_LEAVE      = 0x02
MSG_LOBBY_START_VOTE = 0x03
MSG_LOBBY_START_ACK  = 0x04
MSG_HELLO            = 0x05
MSG_HELLO_ACK        = 0x06
MSG_SEED_COMMIT      = 0x07
MSG_SEED_REVEAL      = 0x08
MSG_RING_CONFIRM     = 0x09
MSG_CARD_COMMIT      = 0x0A
MSG_CARD_REVEAL      = 0x0B
MSG_ACTION_ANNOUNCE  = 0x0C
MSG_HAND_PASS        = 0x0D
MSG_RESOURCE_QUERY   = 0x0E
MSG_RESOURCE_OFFER   = 0x0F
MSG_RESOURCE_BUY     = 0x10
MSG_AGE_END          = 0x11
MSG_SCORE_REPORT     = 0x12
MSG_GAME_END         = 0x13
MSG_ERROR            = 0x14
MSG_PING             = 0x15
MSG_PONG             = 0x16
MSG_DISCONNECT       = 0x17
MSG_DIRECT_MESSAGE   = 0x18
MSG_GROUP_MESSAGE    = 0x19
MSG_SPECTATOR_SYNC   = 0x20

OPCODE_NAMES = {
    0x01: "LOBBY_PRESENCE", 0x02: "LOBBY_LEAVE", 0x03: "LOBBY_START_VOTE",
    0x04: "LOBBY_START_ACK", 0x05: "HELLO", 0x06: "HELLO_ACK",
    0x07: "SEED_COMMIT", 0x08: "SEED_REVEAL", 0x09: "RING_CONFIRM",
    0x0A: "CARD_COMMIT", 0x0B: "CARD_REVEAL", 0x0C: "ACTION_ANNOUNCE",
    0x0D: "HAND_PASS", 0x0E: "RESOURCE_QUERY", 0x0F: "RESOURCE_OFFER",
    0x10: "RESOURCE_BUY", 0x11: "AGE_END", 0x12: "SCORE_REPORT",
    0x13: "GAME_END", 0x14: "ERROR", 0x15: "PING", 0x16: "PONG",
    0x17: "DISCONNECT", 0x18: "DIRECT_MESSAGE", 0x19: "GROUP_MESSAGE",
    0x20: "SPECTATOR_SYNC"
}

UNRELIABLE_MESSAGES = {
    MSG_LOBBY_PRESENCE, MSG_LOBBY_LEAVE, MSG_LOBBY_START_VOTE,
    MSG_LOBBY_START_ACK, MSG_PING, MSG_PONG, MSG_DISCONNECT, MSG_SPECTATOR_SYNC
}

FLAG_ACK = 0x01
FLAG_RETRANSMIT = 0x02

HEADER_FORMAT = "!BBBB 16s H H I I"
HEADER_SIZE = struct.calcsize(HEADER_FORMAT)
assert HEADER_SIZE == 32

RTO_INIT = 0.200
RTO_MAX = 3.200
RETRY_MAX = 6
T_LOBBY_ANNOUNCE_INTERVAL = 2.0
T_LOBBY_STALE = 6.0
T_LOBBY_QUIET = 3.0
T_LOBBY_TIMEOUT = 120.0
MIN_PLAYERS = 3
MAX_PLAYERS = 7

def clip_text(text: str, limit: int = 1000) -> str:
    """RFC 8.3: chat text must be <= 1000 bytes of UTF-8."""
    return text.encode("utf-8")[:limit].decode("utf-8", "ignore")


class Peer7WDNode:
    def __init__(self, display_name: str, room_code: str, host: str, game_port: int,
                 lobby_port: int = 7777, verbose: bool = False, spectator: bool = False,
                 card_db: str = "Card Database 7WD.xlsx"):
        self.display_name = display_name
        self.room_code = room_code
        self.host = host
        self.game_port = game_port
        self.lobby_port = lobby_port
        self.verbose = verbose
        self.spectator = spectator
        self.running = True

        self.session_id = sha256_hash(room_code.encode("utf-8"))[:16]
        self.lobby_peer_id = os.urandom(16).hex()
        self.manifest_peer_id = 0xFFFF

        self.lobby_roster: Dict[str, dict] = {}
        self.last_roster_change = time.time()
        self.seeking_start_time = time.time()
        self.lobby_closed = False
        self.collected_start_acks: Set[str] = set()

        self.manifest: Dict[int, Tuple[str, int]] = {}
        self.manifest_names: Dict[int, str] = {}
        self.spectator_addrs: Set[Tuple[str, int]] = set()

        self.channel_seq: Dict[int, int] = {}
        self.channel_highest_ack: Dict[int, int] = {}
        self.unacked_packets: Dict[Tuple[int, int], dict] = {}
        self.channel_rto: Dict[int, float] = {}
        self.channel_rtt: Dict[int, float] = {}
        self.channel_rto_base: Dict[int, float] = {}
        self.delivered_seqs: Dict[int, Set[int]] = {}

        self.my_nonce = os.urandom(32)
        self.my_commitment = sha256_hex(self.my_nonce)
        self.collected_commits: Dict[int, str] = {}
        self.collected_reveals: Dict[int, bytes] = {}
        self.shared_seed: Optional[bytes] = None
        self.seating_order: List[int] = []
        self.my_seat = 0
        self.my_wonder_board: Dict[str, Any] = {}
        self.all_wonders: Dict[int, Dict[str, Any]] = {}

        self.card_engine = CardDatabaseEngine(card_db)
        self.current_age = 1
        self.current_turn = 1
        self.current_hand: List[Dict[str, Any]] = []

        self.coins = 3
        self.resources = {r: 0 for r in RESOURCE_KEYS}
        self.trade_discounts = {"raw_left": 2, "raw_right": 2, "mfg": 2}
        self.built_cards: List[Dict[str, Any]] = []
        self.military_shields = 0
        self.military_tokens: List[int] = []
        self.science_symbols: List[str] = []
        self.wonder_stages_built = 0

        self.public_tableaus: Dict[int, Dict[str, Any]] = {}

        self.card_commits: Dict[int, str] = {}
        self.card_reveals: Dict[int, dict] = {}
        self.action_announcements: Dict[int, dict] = {}
        self.age_end_shields: Dict[int, int] = {}
        self.collected_score_reports: Dict[int, dict] = {}

        self.chosen_card: Optional[Dict[str, Any]] = None
        self.chosen_action: str = "BUILD"
        self.chosen_nonce: bytes = b""
        self.revealed_this_turn = False
        self.announced_this_turn = False

        self.incident_reports: Dict[str, Set[int]] = {}
        self.disconnected_peers: Set[int] = set()
        self.state_lock = threading.Lock()

        # UDP Sockets Setup
        self.game_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.game_sock.bind((self.host, self.game_port))

        self.lobby_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.lobby_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            self.lobby_sock.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
            self.lobby_sock.bind(("", self.lobby_port))
        except Exception:
            self.lobby_sock.bind((self.host, self.lobby_port))

        threading.Thread(target=self._lobby_listener, daemon=True).start()
        threading.Thread(target=self._game_listener, daemon=True).start()
        threading.Thread(target=self._retransmission_daemon, daemon=True).start()
        threading.Thread(target=self._lobby_gossip_daemon, daemon=True).start()

    def log(self, direction: str, addr: Tuple[str, int], opcode: int, seq: int, ack: int, flags: int, payload: dict):
        if not self.verbose:
            return
        name = OPCODE_NAMES.get(opcode, f"0x{opcode:02X}")
        ts = time.strftime("%H:%M:%S")
        flag_str = ""
        if flags & FLAG_ACK: flag_str += "[ACK]"
        if flags & FLAG_RETRANSMIT: flag_str += "[RETX]"
        print(f"[{ts}] [{direction}] {addr[0]}:{addr[1]} | {name} (0x{opcode:02X}) | Seq={seq} Ack={ack} {flag_str}")
        print(f"       Payload: {json.dumps(payload)}")

    def pack_packet(self, opcode: int, payload: dict, seq: int = 0, ack: int = 0, flags: int = 0) -> bytes:
        body = json.dumps(payload).encode("utf-8")
        header = struct.pack(
            HEADER_FORMAT, 1, opcode, flags, 0, self.session_id,
            self.manifest_peer_id, len(body), seq, ack
        )
        return header + body

    def unpack_packet(self, data: bytes) -> Tuple[int, int, int, bytes, int, int, int, dict]:
        if len(data) < HEADER_SIZE:
            raise ValueError("Datagram smaller than 32-byte header")
        ver, opcode, flags, reserved, sess_id, sender_pid, plen, seq, ack = struct.unpack(
            HEADER_FORMAT, data[:HEADER_SIZE]
        )
        if ver != 1:
            raise ValueError(f"Unsupported protocol version {ver}")
        body_bytes = data[HEADER_SIZE:HEADER_SIZE + plen]
        payload = json.loads(body_bytes.decode("utf-8")) if plen > 0 else {}
        return opcode, flags, sender_pid, sess_id, plen, seq, ack, payload

    def send_reliable(self, target_pid: int, opcode: int, payload: dict):
        if target_pid not in self.manifest or self.spectator:
            return
        addr = self.manifest[target_pid]

        with self.state_lock:
            cur_seq = self.channel_seq.get(target_pid, 1)
            self.channel_seq[target_pid] = cur_seq + 1
            ack_to_piggyback = self.channel_highest_ack.get(target_pid, 0)
            flags = FLAG_ACK if ack_to_piggyback > 0 else 0

            raw = self.pack_packet(opcode, payload, seq=cur_seq, ack=ack_to_piggyback, flags=flags)
            self.unacked_packets[(target_pid, cur_seq)] = {
                "raw": raw, "addr": addr, "target_pid": target_pid, "opcode": opcode,
                "retries": 0, "last_sent": time.time(), "payload": payload, "seq": cur_seq
            }

        self.game_sock.sendto(raw, addr)
        self.log("SENT", addr, opcode, cur_seq, ack_to_piggyback, flags, payload)

    def send_unreliable(self, addr: Tuple[str, int], opcode: int, payload: dict, ack_target: int = 0):
        flags = FLAG_ACK if ack_target > 0 else 0
        raw = self.pack_packet(opcode, payload, seq=0, ack=ack_target, flags=flags)
        try:
            self.game_sock.sendto(raw, addr)
        except Exception:
            pass
        self.log("SENT", addr, opcode, 0, ack_target, flags, payload)

    def send_bare_ack(self, target_pid: int, ack_number: int):
        if target_pid in self.manifest:
            addr = self.manifest[target_pid]
            raw = self.pack_packet(0, {}, seq=0, ack=ack_number, flags=FLAG_ACK)
            try:
                self.game_sock.sendto(raw, addr)
            except Exception:
                pass
            self.log("SENT", addr, 0, 0, ack_number, FLAG_ACK, {})

    def broadcast_mesh(self, opcode: int, payload: dict, reliable: bool = True):
        for pid in list(self.manifest.keys()):
            if pid != self.manifest_peer_id and pid not in self.disconnected_peers:
                if reliable and (opcode not in UNRELIABLE_MESSAGES):
                    self.send_reliable(pid, opcode, payload)
                else:
                    self.send_unreliable(self.manifest[pid], opcode, payload)

        for s_addr in list(self.spectator_addrs):
            self.send_unreliable(s_addr, opcode, payload)

    def _retransmission_daemon(self):
        while self.running:
            now = time.time()
            to_resend = []
            to_exhaust = []

            with self.state_lock:
                for (target_pid, seq), item in list(self.unacked_packets.items()):
                    rto = self.channel_rto.get(target_pid, RTO_INIT)
                    if now - item["last_sent"] >= rto:
                        if item["retries"] < RETRY_MAX:
                            item["retries"] += 1
                            item["last_sent"] = now
                            new_rto = min(RTO_MAX, rto * 2.0)
                            self.channel_rto[target_pid] = new_rto
                            to_resend.append(item)
                        else:
                            to_exhaust.append(((target_pid, seq), item))

                for key, _ in to_exhaust:
                    del self.unacked_packets[key]

            for item in to_resend:
                raw_with_retx = self.pack_packet(
                    item["opcode"], item["payload"], seq=item["seq"],
                    ack=self.channel_highest_ack.get(item["target_pid"], 0),
                    flags=FLAG_RETRANSMIT
                )
                try:
                    self.game_sock.sendto(raw_with_retx, item["addr"])
                except Exception:
                    pass
                self.log("RETRY", item["addr"], item["opcode"], item["seq"], 0, FLAG_RETRANSMIT, item["payload"])

            time.sleep(0.02)

    def _lobby_gossip_daemon(self):
        while self.running:
            payload = {
                "lobby_peer_id": self.lobby_peer_id,
                "display_name": self.display_name,
                "host": self.host,
                "port": self.game_port,
                "spectator": self.spectator
            }
            raw = self.pack_packet(MSG_LOBBY_PRESENCE, payload, seq=0, ack=0)
            self.log("SENT", ("<broadcast>", self.lobby_port), MSG_LOBBY_PRESENCE, 0, 0, 0, payload)

            try:
                self.lobby_sock.sendto(raw, ("<broadcast>", self.lobby_port))
            except Exception:
                pass
            try:
                self.lobby_sock.sendto(raw, ("127.0.0.1", self.lobby_port))
            except Exception:
                pass

            for target_port in (9001, 9002, 9003, 9004, 9005):
                if target_port != self.game_port:
                    try:
                        self.game_sock.sendto(raw, ("127.0.0.1", target_port))
                    except Exception:
                        pass

            now = time.time()
            with self.state_lock:
                stale = [lpid for lpid, info in self.lobby_roster.items() if now - info["last_seen"] > T_LOBBY_STALE]
                for lpid in stale:
                    del self.lobby_roster[lpid]
                    self.last_roster_change = now

            if not self.spectator and not self.lobby_closed:
                player_roster_count = sum(1 for info in self.lobby_roster.values() if not info.get("spectator", False)) + 1
                if MIN_PLAYERS <= player_roster_count <= MAX_PLAYERS:
                    if (now - self.last_roster_change >= T_LOBBY_QUIET) or (now - self.seeking_start_time >= T_LOBBY_TIMEOUT):
                        self._propose_lobby_start()

            time.sleep(T_LOBBY_ANNOUNCE_INTERVAL)

    def _propose_lobby_start(self):
        player_lpids = [lpid for lpid, info in self.lobby_roster.items() if not info.get("spectator", False)]
        player_lpids.append(self.lobby_peer_id)
        sorted_participants = sorted(player_lpids)

        payload = {"participants": sorted_participants}
        raw = self.pack_packet(MSG_LOBBY_START_VOTE, payload)
        self.log("SENT", ("<broadcast>", self.lobby_port), MSG_LOBBY_START_VOTE, 0, 0, 0, payload)

        targets = [("<broadcast>", self.lobby_port), ("127.0.0.1", self.lobby_port)]
        for info in self.lobby_roster.values():
            targets.append((info["host"], info["port"]))
        for s_addr in self.spectator_addrs:
            targets.append(s_addr)

        for dest in targets:
            try:
                self.game_sock.sendto(raw, dest)
            except Exception:
                pass

    def _handle_presence_packet(self, payload: dict, addr: Tuple[str, int]):
        lpid = payload.get("lobby_peer_id")
        if not lpid or lpid == self.lobby_peer_id:
            return

        is_spec = payload.get("spectator", False)
        with self.state_lock:
            if is_spec:
                spec_tuple = (payload.get("host", addr[0]), payload.get("port", addr[1]))
                if spec_tuple not in self.spectator_addrs:
                    self.spectator_addrs.add(spec_tuple)
                    print(f"[*] Spectator Connected: '{payload['display_name']}' @ {spec_tuple[0]}:{spec_tuple[1]}")
                    if self.shared_seed is not None and not self.spectator:
                        sync_data = {
                            "seating_order": self.seating_order,
                            "manifest_names": self.manifest_names,
                            "all_wonders": self.all_wonders,
                            "public_tableaus": self.public_tableaus,
                            "age": self.current_age,
                            "turn": self.current_turn
                        }
                        self.send_unreliable(spec_tuple, MSG_SPECTATOR_SYNC, sync_data)
            else:
                if lpid not in self.lobby_roster:
                    self.last_roster_change = time.time()
                    if not self.lobby_closed:
                        print(f"[*] Discovered Player: '{payload['display_name']}' ({payload['host']}:{payload['port']})")
                self.lobby_roster[lpid] = {
                    "display_name": payload["display_name"],
                    "host": payload["host"],
                    "port": payload["port"],
                    "spectator": False,
                    "last_seen": time.time()
                }

    def _handle_lobby_packet(self, opcode: int, payload: dict, addr: Tuple[str, int]):
        if opcode == MSG_LOBBY_PRESENCE:
            self._handle_presence_packet(payload, addr)

        elif opcode == MSG_LOBBY_START_VOTE and not self.lobby_closed:
            proposed = payload.get("participants", [])
            if self.spectator:
                self._finalize_lobby_and_start(proposed)
                return

            player_lpids = [lpid for lpid, info in self.lobby_roster.items() if not info.get("spectator", False)]
            player_lpids.append(self.lobby_peer_id)
            my_full_roster = sorted(player_lpids)

            if proposed == my_full_roster:
                p_hash = sha256_hex(json.dumps(proposed).encode("utf-8"))
                ack_payload = {
                    "lobby_peer_id": self.lobby_peer_id,
                    "participants_hash": p_hash
                }
                ack_pkt = self.pack_packet(MSG_LOBBY_START_ACK, ack_payload)
                self.log("SENT", ("<broadcast>", self.lobby_port), MSG_LOBBY_START_ACK, 0, 0, 0, ack_payload)

                targets = [("<broadcast>", self.lobby_port), ("127.0.0.1", self.lobby_port)]
                for info in self.lobby_roster.values():
                    targets.append((info["host"], info["port"]))
                for s_addr in self.spectator_addrs:
                    targets.append(s_addr)

                for dest in targets:
                    try:
                        self.game_sock.sendto(ack_pkt, dest)
                    except Exception:
                        pass

                self.collected_start_acks.add(self.lobby_peer_id)
                if len(self.collected_start_acks) >= len(my_full_roster):
                    self._finalize_lobby_and_start(my_full_roster)

        elif opcode == MSG_LOBBY_START_ACK and not self.lobby_closed:
            if self.spectator:
                return
            player_lpids = [lpid for lpid, info in self.lobby_roster.items() if not info.get("spectator", False)]
            player_lpids.append(self.lobby_peer_id)
            my_full_roster = sorted(player_lpids)
            expected_hash = sha256_hex(json.dumps(my_full_roster).encode("utf-8"))

            if payload.get("participants_hash") == expected_hash:
                ack_sender_lpid = payload.get("lobby_peer_id")
                if ack_sender_lpid:
                    self.collected_start_acks.add(ack_sender_lpid)
                else:
                    self.collected_start_acks.add(addr[0] + ":" + str(addr[1]))

                if len(self.collected_start_acks) >= len(my_full_roster):
                    self._finalize_lobby_and_start(my_full_roster)

    def _lobby_listener(self):
        while self.running:
            try:
                data, addr = self.lobby_sock.recvfrom(65535)
                opcode, flags, sender_pid, sess_id, plen, seq, ack, payload = self.unpack_packet(data)
                if sess_id != self.session_id:
                    continue
                if not (opcode == MSG_LOBBY_PRESENCE and payload.get("lobby_peer_id") == self.lobby_peer_id):
                    self.log("RECV", addr, opcode, seq, ack, flags, payload)
                self._handle_lobby_packet(opcode, payload, addr)
            except Exception:
                pass

    def _finalize_lobby_and_start(self, participants: List[str]):
        if self.lobby_closed:
            return
        self.lobby_closed = True

        for rank, lpid in enumerate(participants, start=1):
            if lpid == self.lobby_peer_id and not self.spectator:
                self.manifest_peer_id = rank
                self.manifest[rank] = (self.host, self.game_port)
                self.manifest_names[rank] = self.display_name
            else:
                pinfo = self.lobby_roster.get(lpid)
                if pinfo:
                    self.manifest[rank] = (pinfo["host"], pinfo["port"])
                    self.manifest_names[rank] = pinfo["display_name"]
                else:
                    self.manifest[rank] = ("127.0.0.1", 9000 + rank)
                    self.manifest_names[rank] = f"Player_{rank}"

        role = "SPECTATOR" if self.spectator else f"PLAYER {self.manifest_peer_id}"
        print(f"\n=======================================================")
        print(f" [+] SESSION STARTED! Role: {role}")
        for pid, addr in self.manifest.items():
            print(f"     Player {pid}: {self.manifest_names[pid]} @ {addr[0]}:{addr[1]}")
        print(f"=======================================================\n")

        if not self.spectator:
            for pid in self.manifest:
                if pid != self.manifest_peer_id:
                    self.send_reliable(pid, MSG_HELLO, {})
        else:
            print("[SPECTATOR] Live monitoring active. Waiting for game to start...\n")

    def start_seed_ceremony(self):
        if self.spectator:
            return
        if self.manifest_peer_id in self.collected_commits:
            return
        print("\n[*] Randomness Ceremony initiated...")
        self.collected_commits[self.manifest_peer_id] = self.my_commitment
        self.broadcast_mesh(MSG_SEED_COMMIT, {"commitment": self.my_commitment})
        self._check_seed_commit_barrier()

    def _handle_seed_commit(self, sender_pid: int, payload: dict):
        self.collected_commits[sender_pid] = payload["commitment"]
        if not self.spectator and self.manifest_peer_id not in self.collected_commits:
            self.start_seed_ceremony()
        self._check_seed_commit_barrier()

    def _check_seed_commit_barrier(self):
        if not self.spectator and len(self.collected_commits) == len(self.manifest):
            if self.manifest_peer_id not in self.collected_reveals:
                self.collected_reveals[self.manifest_peer_id] = self.my_nonce
                self.broadcast_mesh(MSG_SEED_REVEAL, {"nonce": self.my_nonce.hex()})
                self._check_seed_reveal_barrier()

    def _handle_seed_reveal(self, sender_pid: int, payload: dict):
        nonce_bytes = bytes.fromhex(payload["nonce"])
        self.collected_reveals[sender_pid] = nonce_bytes
        self._check_seed_reveal_barrier()

    def _check_seed_reveal_barrier(self):
        req_reveals = len(self.manifest)
        if len(self.collected_reveals) >= req_reveals and self.shared_seed is None:
            concat_nonces = b"".join(self.collected_reveals[pid] for pid in sorted(self.collected_reveals.keys()))
            self.shared_seed = sha256_hash(concat_nonces)

            live_pids = sorted(list(self.manifest.keys()))
            self.seating_order = self.card_engine.derive_ring_seating(self.shared_seed, live_pids)
            self.all_wonders = self.card_engine.assign_wonders(self.shared_seed, self.seating_order)

            for pid in self.seating_order:
                self.public_tableaus[pid] = {
                    "coins": 3,
                    "built_cards": [],
                    "wonder_stages_built": 0,
                    "military_tokens": [],
                    "science_symbols": [],
                    "wonder_board": self.all_wonders[pid]
                }

            if not self.spectator:
                self.my_seat = self.seating_order.index(self.manifest_peer_id)
                self.my_wonder_board = self.all_wonders[self.manifest_peer_id]
                self.resources[self.my_wonder_board["starting_resource"]] += 1
                self.broadcast_mesh(MSG_RING_CONFIRM, {
                    "seat": self.my_seat,
                    "wonder_board": self.my_wonder_board["board"],
                    "wonder_side": self.my_wonder_board["side"]
                })
                self._deal_age(1)
            else:
                print("\n[SPECTATOR] Randomness Ceremony complete! Ring and Wonder boards derived:")
                for s_idx, pid in enumerate(self.seating_order):
                    pname = self.manifest_names.get(pid, f"Player {pid}")
                    wb = self.all_wonders[pid]
                    print(f"  Seat {s_idx}: {pname:<10} | Wonder: {wb['board']} (Side {wb['side']}) | Starts with {wb['starting_resource']}")
                print("\n[SPECTATOR] Age 1 has begun! Live monitoring card drafts...\n")

    def _deal_age(self, age: int):
        self.current_age = age
        self.current_turn = 1
        self.revealed_this_turn = False
        self.announced_this_turn = False
        full_deck = self.card_engine.build_age_deck(self.shared_seed, age, len(self.seating_order))
        self.current_hand = full_deck[self.my_seat * 7 : (self.my_seat + 1) * 7]
        print(f"\n=======================================================")
        print(f"                AGE {age} HAS COMMENCED")
        print(f"=======================================================")
        self._display_hand()

    def _display_hand(self):
        print(f"\n--- Age {self.current_age} | Turn {self.current_turn} / 6 (Seat {self.my_seat}: {self.display_name}) ---")
        res_str = ", ".join(f"{k}:{v}" for k, v in self.resources.items() if v > 0)
        print(f"Coins: {self.coins} | Shields: {self.military_shields} | Production: [{res_str}]")
        print(f"Cards in Hand ({len(self.current_hand)}):")
        for idx, card in enumerate(self.current_hand):
            print(f"  {idx}: {card['name']:<20} | Color: {card['color']:<6} | Cost: {card['cost']:<14} | Chain: {card['chain_from']}")
        print("To act: type 'pick <index> [BUILD / DISCARD / WONDER]'")

    def draft_action(self, card_idx: int, action: str = "BUILD"):
        if self.spectator:
            print("[SPECTATOR] Spectators cannot draft cards.")
            return
        if card_idx < 0 or card_idx >= len(self.current_hand):
            print("Invalid card selection.")
            return

        act = action.upper()
        if act == "WONDER":
            act = "WONDER_STAGE"

        card = self.current_hand[card_idx]
        self.chosen_card = card
        self.chosen_action = act
        self.chosen_nonce = os.urandom(32)

        token = card["card_id"].encode("utf-8") + self.chosen_action.encode("utf-8") + self.chosen_nonce
        commit_digest = sha256_hex(token)

        self.card_commits[self.manifest_peer_id] = commit_digest
        print(f"[*] Committed {self.chosen_action} on '{card['name']}'. Waiting for other players...")

        self.broadcast_mesh(MSG_CARD_COMMIT, {
            "age": self.current_age,
            "turn": self.current_turn,
            "commitment": commit_digest
        })
        self._check_card_commit_barrier()

    def _handle_card_commit(self, sender_pid: int, payload: dict):
        self.card_commits[sender_pid] = payload["commitment"]
        self._check_card_commit_barrier()

    def _check_card_commit_barrier(self):
        if not self.spectator and self.chosen_card is not None and not self.revealed_this_turn:
            if len(self.card_commits) == len(self.seating_order):
                self.revealed_this_turn = True
                reveal_payload = {
                    "age": self.current_age,
                    "turn": self.current_turn,
                    "action": self.chosen_action,
                    "nonce": self.chosen_nonce.hex()
                }
                if self.chosen_action == "BUILD":
                    reveal_payload["card_id"] = self.chosen_card["card_id"]

                self.broadcast_mesh(MSG_CARD_REVEAL, reveal_payload)
                self.card_reveals[self.manifest_peer_id] = reveal_payload
                self._check_card_reveal_barrier()

    def _handle_card_reveal(self, sender_pid: int, payload: dict):
        self.card_reveals[sender_pid] = payload
        self._check_card_reveal_barrier()

    def _check_card_reveal_barrier(self):
        if not self.spectator and self.revealed_this_turn and not self.announced_this_turn:
            if len(self.card_reveals) == len(self.seating_order):
                self.announced_this_turn = True
                self._execute_resolve_and_announce()

    def _execute_resolve_and_announce(self):
        card = self.chosen_card
        action = self.chosen_action
        self.current_hand = [c for c in self.current_hand if c["instance_id"] != card["instance_id"]]

        announce_payload = {
            "action": action,
            "age": self.current_age,
            "turn": self.current_turn,
            "peer_name": self.display_name
        }

        if action == "BUILD":
            coins_req, _ = parse_card_cost(card["cost"])
            is_chained = verify_chaining(card, self.built_cards)
            cost_paid = {"coins": 0 if is_chained else coins_req, "resources_bought": []}

            self.coins -= cost_paid["coins"]
            self.built_cards.append(card)
            self._apply_card_effects(card)

            announce_payload["card_id"] = card["card_id"]
            announce_payload["cost_paid"] = cost_paid

        elif action == "WONDER_STAGE":
            self.wonder_stages_built += 1
            announce_payload["stage_index"] = self.wonder_stages_built

        elif action == "DISCARD":
            self.coins += 3

        self.action_announcements[self.manifest_peer_id] = announce_payload
        self.broadcast_mesh(MSG_ACTION_ANNOUNCE, announce_payload)
        self._check_action_announce_barrier()

    def _apply_card_effects(self, card: Dict[str, Any]):
        eff = card.get("effect", "")
        color = card.get("color", "")
        if color == "RED":
            shields = 1 if "1 Shield" in eff else 2 if "2 Shields" in eff else 3
            self.military_shields += shields
        elif color in ("BROWN", "GREY"):
            for r in RESOURCE_KEYS:
                if f"Produces 1 {r.capitalize()}" in eff or f"Produces 1 {r}" in eff:
                    self.resources[r] += 1
        elif color == "YELLOW":
            if "3 coins" in eff:
                self.coins += 3
            elif "West Trading Post" in card["name"]:
                self.trade_discounts["raw_left"] = 1
            elif "East Trading Post" in card["name"]:
                self.trade_discounts["raw_right"] = 1
            elif "Marketplace" in card["name"]:
                self.trade_discounts["mfg"] = 1
        elif color == "GREEN":
            sym = "TABLET" if "Tablet" in eff else "COMPASS" if "Compass" in eff else "GEAR"
            self.science_symbols.append(sym)

    def _handle_action_announce(self, sender_pid: int, payload: dict):
        self.action_announcements[sender_pid] = payload
        act = payload.get("action")
        sender_name = payload.get("peer_name", self.manifest_names.get(sender_pid, f"Player {sender_pid}"))
        self.manifest_names[sender_pid] = sender_name

        tab = self.public_tableaus.setdefault(sender_pid, {"built_cards": [], "coins": 3, "wonder_stages_built": 0})
        if act == "BUILD":
            cid = payload.get("card_id")
            tab["built_cards"].append({"card_id": cid, "color": "UNKNOWN"})
            if self.spectator:
                print(f"[TURN {payload.get('turn')}] {sender_name} BUILT: '{cid}'")
        elif act == "WONDER_STAGE":
            tab["wonder_stages_built"] += 1
            if self.spectator:
                print(f"[TURN {payload.get('turn')}] {sender_name} BUILT WONDER STAGE {tab['wonder_stages_built']}")
        elif act == "DISCARD":
            tab["coins"] += 3
            if self.spectator:
                print(f"[TURN {payload.get('turn')}] {sender_name} DISCARDED for 3 coins")

        self._check_action_announce_barrier()

    def _check_action_announce_barrier(self):
        if not self.spectator and len(self.action_announcements) == len(self.seating_order):
            self._finalize_turn_and_pass()

    def _finalize_turn_and_pass(self):
        self.card_commits.clear()
        self.card_reveals.clear()
        self.action_announcements.clear()
        self.chosen_card = None
        self.revealed_this_turn = False
        self.announced_this_turn = False

        k = len(self.seating_order)
        direction = -1 if self.current_age in (1, 3) else 1
        neighbor_seat = (self.my_seat + direction) % k
        target_pid = self.seating_order[neighbor_seat]

        if self.current_turn == 6:
            print(f"\n[*] Turn 6 finished. Unplayed card silently set aside.")
            self.current_hand.clear()
            # RFC 7.8: the Turn 6 HAND_PASS is still sent, but with an EMPTY cards array
            self.send_reliable(target_pid, MSG_HAND_PASS, {
                "age": self.current_age, "turn": 6, "cards": []
            })
            self._resolve_military_age_end()
            return

        pass_payload = {
            "age": self.current_age,
            "turn": self.current_turn,
            "cards": [c["card_id"] for c in self.current_hand]
        }
        self.send_reliable(target_pid, MSG_HAND_PASS, pass_payload)

    def _handle_hand_pass(self, sender_pid: int, payload: dict):
        if self.spectator: return
        if payload.get("turn") == 6:
            return  # Turn 6 pass carries an empty hand: nothing to deal, and the Age is ending
        cids = payload.get("cards", [])
        new_hand = []
        for cid in cids:
            card = self.card_engine.lookup_card(cid)   # works for Age I/II/III cards AND guilds
            if card is None:
                print(f"[!] HAND_PASS contained unknown card_id '{cid}'")
                continue
            card["instance_id"] = f"{cid}_{os.urandom(4).hex()}"
            new_hand.append(card)

        self.current_hand = new_hand
        self.current_turn += 1
        self._display_hand()

    def _resolve_military_age_end(self):
        print(f"\n[*] Broadcasting military shields for Age {self.current_age} resolution...")
        self.age_end_shields[self.manifest_peer_id] = self.military_shields
        self.broadcast_mesh(MSG_AGE_END, {
            "age": self.current_age,
            "shields": self.military_shields,
            "peer_name": self.display_name
        })

    def _handle_age_end(self, sender_pid: int, payload: dict):
        self.age_end_shields[sender_pid] = payload["shields"]

        if self.spectator and len(self.age_end_shields) == len(self.seating_order):
            print(f"\n[SPECTATOR] Age {payload.get('age')} Ended! Military Results:")
            for pid, sh in self.age_end_shields.items():
                pname = self.manifest_names.get(pid, f"Player {pid}")
                print(f"  {pname}: {sh} shields")
            self.age_end_shields.clear()

        if not self.spectator and len(self.age_end_shields) == len(self.seating_order):
            k = len(self.seating_order)
            left_pid = self.seating_order[(self.my_seat - 1) % k]
            right_pid = self.seating_order[(self.my_seat + 1) % k]

            win_vp = 1 if self.current_age == 1 else 3 if self.current_age == 2 else 5
            if self.military_shields > self.age_end_shields[left_pid]:
                self.military_tokens.append(win_vp)
                print(f"[MILITARY] Victory vs Left Neighbor (Peer {left_pid})! (+{win_vp} VP)")
            elif self.military_shields < self.age_end_shields[left_pid]:
                self.military_tokens.append(-1)
                print(f"[MILITARY] Defeat vs Left Neighbor (Peer {left_pid})! (-1 VP)")

            if self.military_shields > self.age_end_shields[right_pid]:
                self.military_tokens.append(win_vp)
                print(f"[MILITARY] Victory vs Right Neighbor (Peer {right_pid})! (+{win_vp} VP)")
            elif self.military_shields < self.age_end_shields[right_pid]:
                self.military_tokens.append(-1)
                print(f"[MILITARY] Defeat vs Right Neighbor (Peer {right_pid})! (-1 VP)")

            self.age_end_shields.clear()
            if self.current_age < 3:
                self._deal_age(self.current_age + 1)
            else:
                self._compute_and_broadcast_scores()

    def _compute_and_broadcast_scores(self):
        print("\n[*] Game End: Computing 7-category independent final scores (RFC 7.11)...")
        self.public_tableaus[self.manifest_peer_id] = {
            "coins": self.coins,
            "military_tokens": self.military_tokens,
            "wonder_stages_built": self.wonder_stages_built,
            "built_cards": self.built_cards,
            "science_symbols": self.science_symbols,
            "wonder_board": self.my_wonder_board
        }

        all_computed = compute_all_scores(self.seating_order, self.public_tableaus)
        my_report = all_computed[self.manifest_peer_id]
        self.collected_score_reports[self.manifest_peer_id] = my_report
        self.broadcast_mesh(MSG_SCORE_REPORT, my_report)

    def _handle_score_report(self, sender_pid: int, payload: dict):
        self.collected_score_reports[sender_pid] = payload
        if len(self.collected_score_reports) == len(self.seating_order):
            print("\n======================= FINAL SCOREBOARD =======================")
            ranked = []
            for pid, sc in self.collected_score_reports.items():
                ranked.append((pid, sc["total"], self.public_tableaus[pid].get("coins", 0), sc))
            ranked.sort(key=lambda x: (x[1], x[2]), reverse=True)

            for rank, (pid, tot, c, sc) in enumerate(ranked, start=1):
                pname = self.manifest_names.get(pid, f"Player {pid}")
                print(f"Rank {rank}: {pname:<12} (Seat {self.seating_order.index(pid)}) | Score: {tot:2} VP | Coins: {c} | Breakdown: {sc}")
            print("================================================================\n")

            if not self.spectator:
                winner_pid = ranked[0][0]
                winner_seat = self.seating_order.index(winner_pid)
                final_scores_payload = [
                    {"seat": self.seating_order.index(p), "total": s["total"], "coins": self.public_tableaus[p].get("coins", 0)}
                    for p, s in self.collected_score_reports.items()
                ]
                self.broadcast_mesh(MSG_GAME_END, {
                    "winner_seat": winner_seat,
                    "final_scores": final_scores_payload
                })

    def print_spectator_dashboard(self):
        print("\n================ LIVE SPECTATOR DASHBOARD ================")
        display_pids = self.seating_order if self.seating_order else sorted(list(self.public_tableaus.keys()))
        if not display_pids and self.manifest:
            display_pids = sorted(list(self.manifest.keys()))

        if not display_pids:
            print("No player data received yet.")
            print("==========================================================\n")
            return

        for pid in display_pids:
            pname = self.manifest_names.get(pid, f"Player {pid}")
            tab = self.public_tableaus.get(pid, {})
            b_cnt = len(tab.get("built_cards", []))
            w_st = tab.get("wonder_stages_built", 0)
            c = tab.get("coins", 3)
            seat_str = f"Seat {self.seating_order.index(pid)}" if (self.seating_order and pid in self.seating_order) else f"Player {pid}"
            print(f"{seat_str:<10}: {pname:<10} | Built Structures: {b_cnt:2} | Wonder Stages: {w_st} | Coins: {c}")
        print("==========================================================\n")

    def _game_listener(self):
        while self.running:
            try:
                data, addr = self.game_sock.recvfrom(65535)
                opcode, flags, sender_pid, sess_id, plen, seq, ack, payload = self.unpack_packet(data)
                self.log("RECV", addr, opcode, seq, ack, flags, payload)

                if flags & FLAG_ACK and ack > 0:
                    with self.state_lock:
                        if (sender_pid, ack) in self.unacked_packets:
                            del self.unacked_packets[(sender_pid, ack)]
                            # RFC 6.3: a successful ACK resets the RTO (to the RTT-seeded base if we have one)
                            self.channel_rto[sender_pid] = self.channel_rto_base.get(sender_pid, RTO_INIT)

                if opcode not in UNRELIABLE_MESSAGES and seq > 0 and not self.spectator:
                    with self.state_lock:
                        self.channel_highest_ack[sender_pid] = max(
                            self.channel_highest_ack.get(sender_pid, 0), seq
                        )
                        if seq in self.delivered_seqs.setdefault(sender_pid, set()):
                            self.send_bare_ack(sender_pid, seq)
                            continue
                        self.delivered_seqs[sender_pid].add(seq)
                    self.send_bare_ack(sender_pid, seq)

                # Route all lobby opcodes arrived on game_sock
                if opcode in (MSG_LOBBY_PRESENCE, MSG_LOBBY_START_VOTE, MSG_LOBBY_START_ACK):
                    self._handle_lobby_packet(opcode, payload, addr)
                elif opcode == MSG_SPECTATOR_SYNC and self.spectator:
                    self.seating_order = payload.get("seating_order", [])
                    self.manifest_names = {int(k): v for k, v in payload.get("manifest_names", {}).items()}
                    self.all_wonders = {int(k): v for k, v in payload.get("all_wonders", {}).items()}
                    self.public_tableaus = {int(k): v for k, v in payload.get("public_tableaus", {}).items()}
                    self.current_age = payload.get("age", 1)
                    self.current_turn = payload.get("turn", 1)
                    self.lobby_closed = True
                    print(f"\n[SPECTATOR] Synchronized with live game! (Age {self.current_age}, Turn {self.current_turn})")
                    self.print_spectator_dashboard()
                elif opcode == MSG_HELLO and not self.spectator:
                    self.send_reliable(sender_pid, MSG_HELLO_ACK, {})
                elif opcode == MSG_PING and not self.spectator:
                    self.send_unreliable(addr, MSG_PONG, {"echo_sent_at_ms": payload.get("sent_at_ms", 0)})
                elif opcode == MSG_PONG:
                    rtt = (time.time() * 1000) - payload.get("echo_sent_at_ms", time.time() * 1000)
                    self.channel_rtt[sender_pid] = rtt / 1000.0
                    self.channel_rto_base[sender_pid] = max(0.200, min(RTO_MAX, (rtt / 1000.0) * 2.5))
                    self.channel_rto[sender_pid] = self.channel_rto_base[sender_pid]
                elif opcode == MSG_SEED_COMMIT:
                    self._handle_seed_commit(sender_pid, payload)
                elif opcode == MSG_SEED_REVEAL:
                    self._handle_seed_reveal(sender_pid, payload)
                elif opcode == MSG_RING_CONFIRM:
                    if sender_pid not in self.seating_order:
                        self.seating_order.append(sender_pid)
                elif opcode == MSG_CARD_COMMIT:
                    self._handle_card_commit(sender_pid, payload)
                elif opcode == MSG_CARD_REVEAL:
                    self._handle_card_reveal(sender_pid, payload)
                elif opcode == MSG_ACTION_ANNOUNCE:
                    self._handle_action_announce(sender_pid, payload)
                elif opcode == MSG_HAND_PASS:
                    self._handle_hand_pass(sender_pid, payload)
                elif opcode == MSG_AGE_END:
                    self._handle_age_end(sender_pid, payload)
                elif opcode == MSG_SCORE_REPORT:
                    self._handle_score_report(sender_pid, payload)
                elif opcode == MSG_GAME_END:
                    print("\n[+] Consensus reached: GAME_END broadcast confirmed.")
                elif opcode == MSG_DIRECT_MESSAGE:
                    print(f"\n[DM from Peer {sender_pid}]: {payload.get('text')}")
                elif opcode == MSG_GROUP_MESSAGE:
                    print(f"\n[GROUP CHAT]: {payload.get('text')}")
                elif opcode == MSG_ERROR:
                    print(f"\n[!] ERROR BROADCAST: {payload.get('code')} -> {payload.get('detail')}")

            except ConnectionResetError:
                continue  # Windows: ICMP "port unreachable" from a peer that isn't running yet
            except Exception as e:
                print(f"[!] _game_listener error: {type(e).__name__}: {e}")


def main():
    parser = argparse.ArgumentParser(description="7 Wonders Peer Node (RFC 7WD-1)")
    parser.add_argument("--name", required=True, help="Player or spectator name")
    parser.add_argument("--room", default="cs-demo", help="Room code for Lobby hash derivation")
    parser.add_argument("--port", type=int, required=True, help="Game UDP port")
    parser.add_argument("--host", default="127.0.0.1", help="IP to bind AND advertise to peers (use your LAN IP for multi-PC play)")
    parser.add_argument("--cards", default="Card Database 7WD.xlsx", help="Path to the card database spreadsheet")
    parser.add_argument("--lobby_port", type=int, default=7777, help="Lobby discovery port")
    parser.add_argument("--verbose", action="store_true", default=False, help="Enable verbose network logging")
    parser.add_argument("--spectator", action="store_true", help="Launch in Creative Extension Spectator Role (Bonus 10 pts)")
    args = parser.parse_args()

    node = Peer7WDNode(
        display_name=args.name,
        room_code=args.room,
        host=args.host,
        game_port=args.port,
        lobby_port=args.lobby_port,
        verbose=args.verbose,
        spectator=args.spectator,
        card_db=args.cards
    )

    role_desc = "SPECTATOR MODE (Bonus Extension)" if args.spectator else "PLAYER NODE"
    print(f"=== 7WD Node Started: '{args.name}' | {role_desc} | Game Port: {args.port} | Room: '{args.room}' ===")

    print("\nCommands:")
    if not args.spectator:
        print("  start                    - Start Seed Commit ceremony")
        print("  pick <idx> [action]      - Draft card (action: BUILD, DISCARD, WONDER)")
        print("  trade <left/right> <res> - Query neighbor for resource")
    else:
        print("  board                    - Display live spectator overview")
    print("  dm <peer_id> <text>      - Send DIRECT_MESSAGE (0x18)")
    print("  msg <text>               - Send GROUP_MESSAGE (0x19)")
    print("  ping <peer_id>           - Ping peer to test RTT/RTO")
    print("  verbose                  - Toggle runtime verbose mode on/off")
    print("  roster                   - Show manifest and seating order")
    print("  quit                     - Exit node\n")

    while node.running:
        try:
            line = input().strip()
            if not line:
                continue
            parts = line.split(" ", 2)
            cmd = parts[0].lower()

            if cmd == "start" and not node.spectator:
                node.start_seed_ceremony()
            elif cmd == "board" and node.spectator:
                node.print_spectator_dashboard()
            elif cmd == "pick" and not node.spectator and len(parts) > 1:
                action = parts[2].upper() if len(parts) > 2 else "BUILD"
                node.draft_action(int(parts[1]), action)
            elif cmd == "dm" and len(parts) > 2:
                node.send_reliable(int(parts[1]), MSG_DIRECT_MESSAGE, {"text": clip_text(parts[2])})
            elif cmd == "msg" and len(parts) > 1:
                node.broadcast_mesh(MSG_GROUP_MESSAGE, {"text": clip_text(line.split(" ", 1)[1])})
            elif cmd == "ping" and len(parts) > 1:
                target_pid = int(parts[1])
                if target_pid in node.manifest:
                    node.send_unreliable(node.manifest[target_pid], MSG_PING, {"sent_at_ms": int(time.time() * 1000)})
            elif cmd == "verbose":
                node.verbose = not node.verbose
                print(f"[*] Verbose Logging: {'ENABLED' if node.verbose else 'DISABLED'}")
            elif cmd == "roster":
                print(f"Manifest: {node.manifest_names}")
                print(f"Seating Ring: {node.seating_order} (My Seat: {node.my_seat})")
            elif cmd == "quit":
                node.running = False
                break
        except KeyboardInterrupt:
            node.running = False
            break

if __name__ == "__main__":
    main()