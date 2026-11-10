import pandas as pd
import hashlib
import struct
from typing import List, Dict, Tuple, Any

RESOURCE_KEYS = ["WOOD", "ORE", "CLAY", "STONE", "GLASS", "PAPYRUS", "TEXTILE"]

def sha256_hash(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()

def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

class CardDatabaseEngine:
    def __init__(self, excel_path: str = "Card Database 7WD.xlsx"):
        self.excel_path = excel_path
        self.age1_df = self._read_sheet("Age I Cards")
        self.age2_df = self._read_sheet("Age II Cards")
        self.age3_df = self._read_sheet("Age III Cards")
        self.guilds_df = self._read_guilds("Guild Cards (Age III)")
        self.wonders_df = self._read_wonders("Wonder Boards")

    def _read_sheet(self, sheet_name: str) -> pd.DataFrame:
        df = pd.read_excel(self.excel_path, sheet_name=sheet_name, skiprows=2)
        df.columns = [str(col).strip() for col in df.iloc[0]]
        return df.iloc[1:].reset_index(drop=True)

    def _read_guilds(self, sheet_name: str) -> pd.DataFrame:
        df = pd.read_excel(self.excel_path, sheet_name=sheet_name, skiprows=2)
        df.columns = [str(col).strip() for col in df.iloc[0]]
        return df.iloc[1:].reset_index(drop=True)

    def _read_wonders(self, sheet_name: str) -> pd.DataFrame:
        df = pd.read_excel(self.excel_path, sheet_name=sheet_name, skiprows=2)
        df.columns = [str(col).strip() for col in df.iloc[0]]
        return df.iloc[1:].reset_index(drop=True)

    def lookup_card(self, card_id: str):
        """Return the full card dict for ANY card_id (Age I/II/III sheets or Guilds), or None."""
        for df in (self.age1_df, self.age2_df, self.age3_df, self.guilds_df):
            sub = df[df["Card Name"].astype(str).str.strip() == card_id]
            if len(sub) > 0:
                row = sub.iloc[0]
                return {
                    "card_id": card_id,
                    "name": card_id,
                    "color": "PURPLE" if df is self.guilds_df else str(row["Color"]).strip().upper(),
                    "cost": str(row.get("Cost to Build", "Free")).strip(),
                    "effect": str(row.get("Effect", "")).strip(),
                    "chain_from": str(row.get("Free-Build After (Chain From)", "—")).strip(),
                    "chain_to": str(row.get("Enables Free Build Of (Chain To)", "—")).strip(),
                }
        return None

    def derive_ring_seating(self, seed: bytes, live_peer_ids: List[int]) -> List[int]:
        scored = []
        for pid in live_peer_ids:
            key = sha256_hash(seed + struct.pack("!B", pid))
            scored.append((key, pid))
        scored.sort(key=lambda x: x[0])
        return [pid for _, pid in scored]

    def assign_wonders(self, seed: bytes, seating: List[int]) -> Dict[int, Dict[str, Any]]:
        unique_boards = sorted(list(self.wonders_df["Board"].unique()))
        scored_boards = []
        for bname in unique_boards:
            key = sha256_hash(seed + bname.encode("utf-8"))
            scored_boards.append((key, bname))
        scored_boards.sort(key=lambda x: x[0])

        assignments = {}
        for seat_idx, pid in enumerate(seating):
            board_name = scored_boards[seat_idx % len(scored_boards)][1]
            side_key = sha256_hash(seed + board_name.encode("utf-8") + b"side")
            side = "B" if (side_key[-1] & 1) == 1 else "A"

            sub = self.wonders_df[(self.wonders_df["Board"] == board_name) & (self.wonders_df["Side"] == side)]
            stages = []
            for _, row in sub.iterrows():
                stages.append({
                    "stage": int(row["Stage"]),
                    "cost": str(row["Cost to Build"]).strip(),
                    "effect": str(row["Effect"]).strip()
                })
            assignments[pid] = {
                "seat": seat_idx,
                "board": board_name,
                "side": side,
                "starting_resource": str(sub.iloc[0]["Starting Resource"]).strip().upper(),
                "stages": stages
            }
        return assignments

    def select_guild_cards(self, seed: bytes, num_players: int) -> List[Dict[str, Any]]:
        scored_guilds = []
        for _, row in self.guilds_df.iterrows():
            cname = str(row["Card Name"]).strip()
            key = sha256_hash(seed + cname.encode("utf-8"))
            card_obj = {
                "card_id": cname,
                "name": cname,
                "color": "PURPLE",
                "cost": str(row.get("Cost to Build", "Free")).strip(),
                "effect": str(row.get("Effect", "")).strip(),
                "chain_from": "—",
                "chain_to": "—"
            }
            scored_guilds.append((key, card_obj))
        scored_guilds.sort(key=lambda x: x[0])
        return [c for _, c in scored_guilds[:(num_players + 2)]]

    def build_age_deck(self, seed: bytes, age: int, num_players: int) -> List[Dict[str, Any]]:
        df_map = {1: self.age1_df, 2: self.age2_df, 3: self.age3_df}
        df = df_map[age]
        count_col = f"Count @{num_players}p"

        deck = []
        for _, row in df.iterrows():
            qty = int(row.get(count_col, 0))
            cname = str(row["Card Name"]).strip()
            color = str(row["Color"]).strip().upper()
            cost = str(row.get("Cost to Build", "Free")).strip()
            effect = str(row.get("Effect", "")).strip()
            chain_from = str(row.get("Free-Build After (Chain From)", "—")).strip()
            chain_to = str(row.get("Enables Free Build Of (Chain To)", "—")).strip()

            for i in range(qty):
                deck.append({
                    "card_id": cname,
                    "name": cname,
                    "color": color,
                    "cost": cost,
                    "effect": effect,
                    "chain_from": chain_from,
                    "chain_to": chain_to,
                    "instance_id": f"{cname}_{i}"
                })

        if age == 3:
            guilds = self.select_guild_cards(seed, num_players)
            for idx, g in enumerate(guilds):
                g_copy = dict(g)
                g_copy["instance_id"] = f"{g['card_id']}_{idx}"
                deck.append(g_copy)

        scored = []
        for card in deck:
            key = sha256_hash(seed + struct.pack("!B", age) + card["instance_id"].encode("utf-8"))
            scored.append((key, card))
        scored.sort(key=lambda x: x[0])
        return [c for _, c in scored]

def parse_card_cost(cost_str: str) -> Tuple[int, Dict[str, int]]:
    coins = 0
    resources = {r: 0 for r in RESOURCE_KEYS}
    if not cost_str or cost_str in ("Free", "—"):
        return coins, resources

    parts = [p.strip() for p in cost_str.split(",")]
    for p in parts:
        tokens = p.split()
        if len(tokens) >= 2:
            try:
                amt = int(tokens[0])
                name = tokens[1].upper()
                if "COIN" in name:
                    coins += amt
                elif name in resources:
                    resources[name] += amt
            except ValueError:
                pass
    return coins, resources

def verify_chaining(card: Dict[str, Any], built_cards: List[Dict[str, Any]]) -> bool:
    chain_from = card.get("chain_from", "—")
    if chain_from and chain_from != "—":
        built_names = {c["card_id"] for c in built_cards}
        if chain_from in built_names:
            return True
    return False

def optimize_science(symbols: List[str]) -> int:
    base_t = symbols.count("TABLET")
    base_c = symbols.count("COMPASS")
    base_g = symbols.count("GEAR")
    wildcards = symbols.count("WILDCARD")

    best_score = 0
    for wt in range(wildcards + 1):
        for wc in range(wildcards + 1 - wt):
            wg = wildcards - wt - wc
            t = base_t + wt
            c = base_c + wc
            g = base_g + wg
            score = (t * t) + (c * c) + (g * g) + (7 * min(t, c, g))
            if score > best_score:
                best_score = score
    return best_score

def compute_all_scores(seating_order: List[int], tableaus: Dict[int, Dict[str, Any]]) -> Dict[int, Dict[str, int]]:
    final_scores = {}
    k = len(seating_order)

    for seat_idx, pid in enumerate(seating_order):
        tab = tableaus[pid]
        left_pid = seating_order[(seat_idx - 1) % k]
        right_pid = seating_order[(seat_idx + 1) % k]
        left_tab = tableaus[left_pid]
        right_tab = tableaus[right_pid]

        mil_score = sum(tab.get("military_tokens", []))
        coins = tab.get("coins", 0)
        treasury_score = coins // 3

        wonder_score = 0
        stages_done = tab.get("wonder_stages_built", 0)
        for st in tab.get("wonder_board", {}).get("stages", [])[:stages_done]:
            eff = st.get("effect", "")
            if "Victory Point" in eff:
                try:
                    wonder_score += int(eff.split()[0])
                except ValueError:
                    pass

        civilian_score = 0
        for card in tab.get("built_cards", []):
            if card.get("color") == "BLUE":
                eff = card.get("effect", "")
                if "Victory Point" in eff:
                    try:
                        civilian_score += int(eff.split()[0])
                    except ValueError:
                        pass

        science_symbols = list(tab.get("science_symbols", []))
        scientific_score = optimize_science(science_symbols)

        commercial_score = 0
        for card in tab.get("built_cards", []):
            if card.get("color") == "YELLOW":
                cname = card.get("card_id", "")
                if cname == "Haven":
                    commercial_score += sum(1 for c in tab.get("built_cards", []) if c.get("color") == "BROWN")
                elif cname == "Lighthouse":
                    commercial_score += sum(1 for c in tab.get("built_cards", []) if c.get("color") == "YELLOW")
                elif cname == "Chamber of Commerce":
                    commercial_score += 2 * sum(1 for c in tab.get("built_cards", []) if c.get("color") == "GREY")
                elif cname == "Arena":
                    commercial_score += 3 * stages_done

        guild_score = 0
        for card in tab.get("built_cards", []):
            if card.get("color") == "PURPLE":
                gname = card.get("card_id", "")
                if gname == "Builders Guild":
                    wonder_sum = left_tab.get("wonder_stages_built", 0) + stages_done + right_tab.get("wonder_stages_built", 0)
                    guild_score += wonder_sum * 1
                elif gname == "Craftsmens Guild":
                    grey_sum = sum(1 for c in left_tab.get("built_cards", []) if c.get("color") == "GREY") + \
                               sum(1 for c in right_tab.get("built_cards", []) if c.get("color") == "GREY")
                    guild_score += grey_sum * 2
                elif gname == "Magistrates Guild":
                    blue_sum = sum(1 for c in left_tab.get("built_cards", []) if c.get("color") == "BLUE") + \
                               sum(1 for c in right_tab.get("built_cards", []) if c.get("color") == "BLUE")
                    guild_score += blue_sum * 1
                elif gname == "Philosophers Guild":
                    green_sum = sum(1 for c in left_tab.get("built_cards", []) if c.get("color") == "GREEN") + \
                                sum(1 for c in right_tab.get("built_cards", []) if c.get("color") == "GREEN")
                    guild_score += green_sum * 1
                elif gname == "Spies Guild":
                    red_sum = sum(1 for c in left_tab.get("built_cards", []) if c.get("color") == "RED") + \
                              sum(1 for c in right_tab.get("built_cards", []) if c.get("color") == "RED")
                    guild_score += red_sum * 1
                elif gname == "Traders Guild":
                    yellow_sum = sum(1 for c in left_tab.get("built_cards", []) if c.get("color") == "YELLOW") + \
                                 sum(1 for c in right_tab.get("built_cards", []) if c.get("color") == "YELLOW")
                    guild_score += yellow_sum * 1
                elif gname == "Shipowners Guild":
                    own_sum = sum(1 for c in tab.get("built_cards", []) if c.get("color") in ("BROWN", "GREY", "PURPLE"))
                    guild_score += own_sum * 1
                elif gname == "Strategists Guild":
                    defeat_tokens = sum(1 for tok in left_tab.get("military_tokens", []) if tok == -1) + \
                                    sum(1 for tok in right_tab.get("military_tokens", []) if tok == -1)
                    guild_score += defeat_tokens * 1

        total = mil_score + treasury_score + wonder_score + civilian_score + scientific_score + commercial_score + guild_score
        final_scores[pid] = {
            "military": mil_score,
            "treasury": treasury_score,
            "wonder": wonder_score,
            "civilian": civilian_score,
            "scientific": scientific_score,
            "commercial": commercial_score,
            "guilds": guild_score,
            "total": total
        }

    return final_scores