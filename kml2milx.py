#!/usr/bin/env python3
"""
cog2milxly.py - Convert Command Ops 2 save files (.cog) straight into map.army
MilX layer files (.milxly). It does not need the game's GameStatExporter.exe.

Usage:
    python cog2milxly.py                 # opens the map window
    python cog2milxly.py save.cog        # opens the map window with that save
    python cog2milxly.py --help          # command-line export (no window)

The window finds the Command Ops 2 folder (CmdOps.exe) from Steam and Windows
install records, or asks once. It draws the save's map from <game>/Maps/<map>.cop
with every unit on it. Click two places you can identify, type their real
lat, lon, then EXPORT IMAGE (PNG of the scene) or EXPORT MILXLY (map.army).
Needs Pillow for drawing: pip install pillow

Unit symbols come from the game's establishment database (the .coe file the
save names, e.g. COTAEstab.coe, or its .xml export). The tool searches for it
near the save; otherwise pick it with "Estab…" or --estab. Without it, symbols
are guessed from unit names. A co2milxly-style co2milx.txt can override the
type-to-symbol table ("Rules…" / --rules); its keys match GameStatExporter's.

Output: one .milxly file per layer (Friendly, Enemy, Objectives), in the
MilX V3.1 layout used by https://github.com/Serpent03/co2milxly. Open each one
in map.army as a layer.

How a .cog file is laid out (reverse-engineered, not official):
  * A 32-byte "POD" header. The game clock is stored at offset 0x32 as minutes
    since 1 Jan 1904.
  * A series of 144-byte blocks: a 16-byte header (class, object id, next block,
    sequence number) followed by 128 bytes of data. Joining an object's blocks
    in sequence order rebuilds the object.
  * Class 92 objects are units, class 103 are orders/tasks, and class 169 are
    objectives.
  * Unit positions are in game-map units (very likely metres), with x going
    east and y going SOUTH from the map's north-west corner.

A save file holds no real-world coordinates, so you georeference it: give 2-4
reference points (an objective/unit, or a typed game "x, y" such as a map
corner) with their real lat/lon. By default this reproduces GameStatExporter's
maths (Web Mercator EPSG:3857) but fits scale + rotation by default, because
some Command Ops maps are not drawn north-up (Elasson is turned about 30°);
--model axis gives GameStatExporter's exact per-axis result. If the save's map
(.cop, in the game's Maps folder) is found, its village/hill names can be used
as reference points. The fit is checked
before export: Command Ops maps are about 1 m per game unit, so a fit far from
that means a reference coordinate is wrong.
"""

import cmath
import collections
import datetime as dt
import html
import json
import math
import os
import re
import struct
import sys

# --------------------------------------------------------------------------
# .cog decoding
# --------------------------------------------------------------------------

BLOCK = 0x90
HDR = 0x20
CLS_UNIT, CLS_TASK, CLS_OBJECTIVE, CLS_SCENARIO = 92, 103, 169, 75
CLS_HUMAN, CLS_FORCECTL = 77, 80

EPOCH = dt.datetime(1904, 1, 1)

# Order type codes seen in saves. Labels marked "?" are educated guesses.
# Order (task) types in the game's own order: the first byte of a task's type
# code indexes this list (taken from the game code inside GameStatExporter).
TASK_TYPES = ["Move", "Dummy", "Probe", "Attack", "Secure", "Secure Crossing", "Destroy", "Assault",
              "Cross River Assault", "Bombard", "On Call Support", "Fire", "Hold", "Defend", "Delay",
              "Withdraw", "Exit", "Rest", "Reorg", "Construct Bridge", "Deny Crossing"]


def task_type_name(code):
    try:
        k = int(code[:2], 16)
    except (TypeError, ValueError):
        return "Order"
    return TASK_TYPES[k] if k < len(TASK_TYPES) else f"Order {k}"


def _u32(b, o):
    return struct.unpack_from("<I", b, o)[0]


def _i32(b, o):
    return struct.unpack_from("<i", b, o)[0]


def _printable(bs):
    return len(bs) > 0 and all(32 <= c < 127 for c in bs)


def game_time(minutes):
    return EPOCH + dt.timedelta(minutes=minutes)


def fmt_time(t):
    return t.strftime("%d %b %Y %H:%M") if t else ""


class CogError(Exception):
    pass


class CogFile:
    def __init__(self, path):
        self.path = path
        with open(path, "rb") as f:
            self.raw = f.read()
        if self.raw[:4] != b"POD\x00":
            raise CogError("Not a Command Ops save: missing POD header")
        self.objects = self._load_objects()
        self.clock = game_time(_u32(self.raw, 0x32))
        self.title, self.subtitle = self._scenario_title()
        self.forces = self._forces()
        self.units = self._units()
        self.objectives = self._objectives()
        self.human_side = self._human_side()
        self.estab_name, self.map_name = self._referenced_files()
        self.estab = None
        self.intel = self._intel()

    # ---- fog of war ---------------------------------------------------------
    # ScenIntelEnemyForce layout (as decoded): +0x04 believed type (establishment id),
    # +0x08 status (0 known, 1 lost contact, 4 never seen), +0x0A last-seen time,
    # +0x0E/+0x12 believed x/y, +0x1E believed posture, +0x20 believed strength,
    # +0x86 the real unit, +0x8E observing side, +0x94 confidence (0-4096),
    # +0x9C time of the latest report. The save does not record who reported it.
    CLS_INTEL = 94      # ScenIntelEnemyForce: one per unit, held by the opposing side

    def _intel(self):
        """What each side believes about each enemy unit.
        Returns {observer side: {unit id: dict(status, x, y, est_type, est_strength, last_seen)}}.
        status: 'known' (currently tracked), 'last_seen' (lost contact; position is
        where it was last seen, at last_seen), 'unknown' (never seen)."""
        owner = {}
        for sid, b in self.of_class(90):
            for j in range(0, len(b) - 8):
                if b[j:j + 4] == b"\x5e\x00\x00\x00":
                    owner[_u32(b, j + 4)] = sid
        uids = {u["uid"] for u in self.units}
        out = collections.defaultdict(dict)
        for oid, b in self.of_class(self.CLS_INTEL):
            try:
                uid = next((_u32(b, j + 4) for j in range(len(b) - 8)
                            if b[j:j + 4] == b"\x5c\x00\x00\x00" and _u32(b, j + 4) in uids), None)
                if uid is None or oid not in owner:
                    continue
                st = b[8]
                t = _u32(b, 10)
                x, y = _i32(b, 0x0E), _i32(b, 0x12)
                status = {0: "known", 1: "last_seen"}.get(st, "unknown")
                if x < 0 or y < 0:
                    status = "unknown"
                rt = _u32(b, 0x9C) if len(b) >= 0xA0 else 0
                conf = _u32(b, 0x94) if len(b) >= 0x98 else 0
                out[owner[oid]][uid] = dict(
                    status=status, x=x, y=y, est_type=_u32(b, 4), est_strength=_u32(b, 0x20),
                    last_seen=game_time(t) if status == "last_seen" and 0x1000000 < t < 0x2000000 else None,
                    reported=game_time(rt) if 0x1000000 < rt < 0x2000000 else None,
                    confidence=max(0, min(100, round(100 * conf / 4096))) if conf <= 4096 else None,
                    posture=POSTURES[b[0x1E]] if 0 < b[0x1E] < len(POSTURES) else "",
                    estab=None)
            except (struct.error, IndexError):
                continue
        return dict(out)

    def _referenced_files(self):
        """Names of the establishment (.coe) and map (.cop) files the save uses."""
        estab = mapn = None
        for _oid, b in self.of_class(CLS_SCENARIO):
            for s in re.findall(rb"[ -~]{3,}\.co[ep]", b):
                s = s.decode()
                if s.lower().endswith(".coe") and not estab:
                    estab = s
                elif s.lower().endswith(".cop") and not mapn:
                    mapn = s
        return estab, mapn

    def attach_estab(self, estab):
        """Give every unit its establishment entry (type, sub-type, size, HQ)."""
        self.estab = estab
        for u in self.units:
            u["estab"] = estab.forces.get(u["estab_id"]) if estab else None
        for side_intel in self.intel.values():
            for rec in side_intel.values():
                rec["estab"] = estab.forces.get(rec["est_type"]) if estab else None
        return sum(1 for u in self.units if u["estab"]) if estab else 0

    # ---- containers -------------------------------------------------------
    def _load_objects(self):
        parts = collections.defaultdict(dict)
        n = (len(self.raw) - HDR) // BLOCK
        for k in range(n):
            o = HDR + k * BLOCK
            cls, oid, _nxt, seq = struct.unpack_from("<4I", self.raw, o)
            if cls > 100000:  # trailing junk / unaligned tail
                continue
            parts[(cls, oid)][seq] = self.raw[o + 16:o + BLOCK]
        return {k: b"".join(v[s] for s in sorted(v)) for k, v in parts.items()}

    def of_class(self, cls):
        return sorted((k[1], b) for k, b in self.objects.items() if k[0] == cls)

    def _scenario_title(self):
        objs = self.of_class(CLS_SCENARIO)
        if not objs:
            return os.path.basename(self.path), ""
        strings = re.findall(rb"[ -~]{6,}", objs[0][1])
        t = strings[0].decode() if strings else os.path.basename(self.path)
        s = strings[1].decode() if len(strings) > 1 else ""
        return t, s

    def _forces(self):
        """Side id -> commander label, taken from each side's briefing "To:" line."""
        forces = {}
        for oid, b in self.of_class(90):
            m = re.search(rb"To: ([ -~]+)", b)
            forces[oid] = m.group(1).decode().strip() if m else f"Side {oid}"
        return forces

    # ---- units ------------------------------------------------------------
    @staticmethod
    def _unit_names(b):
        for i in range(0x60, min(0x140, len(b) - 8)):
            n = _u32(b, i)
            if 1 <= n <= 12 and _printable(b[i + 4:i + 4 + n]):
                j = i + 4 + n
                m = _u32(b, j)
                if 3 <= m <= 80 and _printable(b[j + 4:j + 4 + m]):
                    return b[i + 4:i + 4 + n].decode(), b[j + 4:j + 4 + m].decode(), j + 4 + m
        for i in range(0x60, min(0x140, len(b) - 8)):
            n = _u32(b, i)
            if 4 <= n <= 80 and _printable(b[i + 4:i + 4 + n]):
                return "", b[i + 4:i + 4 + n].decode(), i + 4 + n
        return None

    def _units(self):
        units = []
        for uid, b in self.of_class(CLS_UNIT):
            nm = self._unit_names(b)
            if not nm:
                continue
            short, name, o = nm
            u = dict(uid=uid, short=short, name=name,
                     x=_u32(b, 0x0E), y=_u32(b, 0x12),
                     status_byte=b[0x1F], side=None, task=None,
                     estab_id=_u32(b, 4), estab=None,
                     personnel=None, equipment=None, ammo=None, rating=None)
            u["offmap"] = (u["status_byte"] == 0x0C)
            try:
                # skip optional strings (empty, or e.g. a unit history text)
                for _ in range(4):
                    n = _u32(b, o)
                    if n == 0:
                        o += 4
                    elif n < 4000 and n != 0x60 and _printable(b[o + 4:o + 4 + min(8, n)]):
                        o += 4 + n
                    else:
                        break
                if _u32(b, o) != 0x60:
                    raise ValueError
                o += 8
                if _u32(b, o) != 0x5A:
                    raise ValueError
                u["side"] = _u32(b, o + 4)
                o += 8
                if _u32(b, o) == CLS_TASK:
                    u["task"] = _u32(b, o + 4)
                    o += 8
                else:
                    o += 4
                if _u32(b, o) != 0x5F:
                    raise ValueError
                o += 8
                if b[o + 1] != 0x05:
                    raise ValueError
                nrefs = _u32(b, o + 2)
                o += 6 + 8 * nrefs
                o += 8 + 4 + 8   # target x,y ; 0 ; ffffffff ffffffff
                a, cur, mx, rating = (_i32(b, o + 4 * i) for i in range(4))
                u.update(personnel=cur, equipment=mx, rating=rating,
                         ammo=(None if a < 0 else max(0, min(100, round(100 * a / 4096)))))
            except (ValueError, struct.error, IndexError):
                pass
            if u["task"]:
                u["order"] = self.task(u["task"])
            else:
                u["order"] = None
            units.append(u)
        # sides for units we could not fully parse: inherit from neighbours by id
        return units

    def task(self, tid):
        b = self.objects.get((CLS_TASK, tid))
        if not b:
            return None
        try:
            o = 1
            o += 4 if _u32(b, o) == 0 else 8
            ts = [_u32(b, o + 4 * i) for i in range(5)]
            i = b.find(b"\xab\x00\x00\x00", o + 20)
            if i < 0:
                return None
            code = b[i + 8:i + 12].hex()
            x, y = _i32(b, i + 16), _i32(b, i + 20)
            return dict(code=code, label=task_type_name(code),
                        x=x, y=y,
                        start=game_time(ts[0]) if 0x1000000 < ts[0] < 0x2000000 else None,
                        due=game_time(ts[1]) if 0x1000000 < ts[1] < 0x2000000 else None)
        except (struct.error, IndexError):
            return None

    # ---- objectives -------------------------------------------------------
    def _objectives(self):
        out = []
        for oid, b in self.of_class(CLS_OBJECTIVE):
            try:
                side = _u32(b, 4)
                t = self.task(_u32(b, 12))
                m = re.search(rb"([\x03-\x40])\x00\x00\x00([ -~]{3,})", b[16:])
                if not t or not m:
                    continue
                s = 16 + m.start()
                name = m.group(2).decode()[:_u32(b, s)]
                held = b[s - 6] == 1
                held_min = _u32(b, s - 4)
                tail = b[s + 4 + len(name):s + 4 + len(name) + 5]
                changed = None
                if len(tail) == 5 and tail[0] == 0 and 0x1000000 < _u32(tail, 1) < 0x2000000:
                    changed = game_time(_u32(tail, 1))
                out.append(dict(oid=oid, side=side, name=name, x=t["x"], y=t["y"],
                                held=held, held_minutes=held_min, changed=changed,
                                points=(_u32(b, 16), _u32(b, 20)),
                                ai=name.startswith("AI-")))
            except (struct.error, IndexError):
                continue
        return out

    # ---- human player -----------------------------------------------------
    def _human_side(self):
        for _oid, b in self.of_class(CLS_HUMAN):
            i = b.find(b"HumanP")
            if i < 0:
                continue
            ctl = _u32(b, i + len("HumanP") + 3)
            pat = struct.pack("<II", CLS_FORCECTL, ctl)
            for uid, ub in self.of_class(CLS_UNIT):
                if pat in ub:
                    for u in self.units:
                        if u["uid"] == uid and u["side"] is not None:
                            return u["side"]
                    # top HQ might not have parsed: read side straight from it
                    j = ub.find(b"\x5a\x00\x00\x00")
                    if j >= 0:
                        return _u32(ub, j + 4)
        return None

    @property
    def sides(self):
        s = sorted({u["side"] for u in self.units if u["side"] is not None} |
                   {o["side"] for o in self.objectives})
        return s


# --------------------------------------------------------------------------
# Military symbology (MIL-STD-2525C SIDC, best effort from unit names)
# --------------------------------------------------------------------------

def echelon_code(name, is_hq):
    n = " " + name + " "
    if re.search(r"\b(Korps|Corps)\b", n):
        return "J"
    if re.search(r"\b(Div|Division)\b", n) and is_hq and "Div Cav" not in n:
        return "I"
    if re.search(r"\b(Bde|Brigade)\b", n) and is_hq:
        return "H"
    if re.search(r"\b(Regt|Regiment|Rgt)\b", n) and is_hq and not re.search(r"\b(Bn|Coy|Bty|Sqn|Pl|Tp)\b", n.replace("Regt", "")):
        return "G"
    if re.search(r"\b(Pl|Tp|Platoon|Troop)\b", n):
        return "D"
    if re.search(r"\b(Coy|Bty|Sqn|Column)\b", n):
        return "E"
    if re.search(r"\b(Bn|Battalion)\b", n):
        return "F"
    return "-"


def function_code(name):
    n = name
    rules = [
        (r"\bBase\b", "USS---"),                        # supply
        (r"\b(Pnr|NZE|Engineer|Pioneer|Bridge|Fd Park|Army Troops)\b", "UCE---"),
        (r"\bFlak\b|\bAA\b", "UCD---"),                  # air defence
        (r"\b(Mor|Mortar|sGrW)\b", "UCFM--"),
        (r"\b(PzJg|AT)\b", "UCAA--"),
        (r"\b(Arty|Fd Bty|Fd Regt|Mdm Bty|Mdm Regt|Inf Gun|RNZA|RAA|RA\b)", "UCF---"),
        (r"\b(AC Coy|Armoured Car)\b", "UCRV--"),
        (r"\b(Recon|Krad|Cav)\b", "UCR---"),
        (r"\b(Pz|Panzer|Tank|Armd)\b", "UCA---"),
        (r"\b(MG)\b", "UCI---"),
        (r"\b(Mot|Schtz|Schuetzen)\b", "UCIM--"),
        (r"\b(GJ|Geb)\b", "UCI---"),
    ]
    for pat, code in rules:
        if re.search(pat, n):
            return code
    return "UCI---"


def sidc_for(unit, friendly_side, rules=None):
    """15-character MIL-STD-2525C SIDC. Uses the unit's establishment entry when
    one is attached (exact), otherwise guesses from the unit's name.
    rules: optional dict from load_ruleset() (co2milxly's co2milx.txt format)."""
    aff = "F" if unit["side"] == friendly_side else "H"
    e = unit.get("estab")
    if e:
        is_hq = e["hq"]
        func = estab_function(e)
        ech = SIZE_ECHELON.get(e["size"], "-")
        if rules and e["key"] in rules:
            s = list(rules[e["key"]].ljust(15, "-")[:15])
            s[1] = aff
            if s[3] == "-":
                s[3] = "P"
            s[11] = ech
            if is_hq:
                s[10] = "A"
            return "".join(s)
    else:
        is_hq = bool(re.search(r"\bHQ\b", unit["name"]))
        func = function_code(unit["name"])
        ech = echelon_code(unit["name"], is_hq)
    mod1 = "A" if is_hq else "-"
    return f"S{aff}GP{func}{mod1}{ech}---"[:15].ljust(15, "-")


# --------------------------------------------------------------------------
# Establishment databases (.coe binary or .xml export)
# --------------------------------------------------------------------------
#
# Each unit in a save stores the id of its "force" (establishment template) at
# offset 4 of its record. In a .coe file, forces are class-48 objects:
#   u32 name length, name, u32 description length, description, then fixed bytes.
#   Relative to the end of the description: +27 picture symbol, +28 is-HQ,
#   +29 type, +30 sub-type, +32 size.
# Codes were checked against the game's own XML exports (COTA, BFTB).

CLS_FORCE = 48

ESTAB_TYPES = {0: "infantry", 1: "armour", 2: "artillery", 3: "logistics"}

# sub-type code -> (GameStatExporter/co2milx key, display name, 2525C function)
ESTAB_SUBTYPES = {
    0: ("infantry", "Infantry", "UCI---"),
    1: ("leginf", "Leg Infantry", "UCI---"),
    2: ("motinf", "Mot Infantry", "UCIM--"),
    3: ("mechinf", "Mech Infantry", "UCIZ--"),
    4: ("parainf", "Para Infantry", "UCIA--"),
    5: ("gliderinf", "Glider Infantry", "UCIA--"),
    6: ("combateng", "Combat Engineer", "UCEC--"),
    7: ("atinf", "AT Infantry", "UCAA--"),
    8: ("smginf", "SMG Infantry", "UCI---"),
    9: ("mginf", "MG Infantry", "UCI---"),
    10: ("hwinf", "Hvy Wpns Infantry", "UCI---"),
    11: ("sf", "Special Forces", "UCI---"),
    12: ("mtninf", "Mountain Infantry", "UCI---"),
    13: ("bicycleinf", "Bicycle Infantry", "UCI---"),
    14: ("cav", "Cavalry", "UCR---"),
    15: ("legrecon", "Leg Recon", "UCR---"),
    16: ("motrecon", "Mot Recon", "UCRV--"),
    17: ("mechrecon", "Mech Recon", "UCRV--"),
    18: ("nonarmhq", "Non-Armoured HQ", None),
    44: ("logistics", "Logistics", "USS---"),
    45: ("base", "Base", "USS---"),
    46: ("bridgeeng", "Bridge Engineer", "UCE---"),
    47: ("consteng", "Construction Engineer", "UCE---"),
    100: ("armour", "Armour", "UCA---"),
    101: ("tank", "Tank", "UCA---"),
    102: ("assaultgun", "Assault Gun", "UCA---"),
    103: ("infsptassaultgun", "Inf Spt Assault Gun", "UCA---"),
    104: ("tankdestroyer", "Tank Destroyer", "UCAA--"),
    105: ("armouredcar", "Armoured Car", "UCAW--"),
    106: ("armouredrecon", "Armoured Recon", "UCRV--"),
    107: ("flamethrowerafv", "Flamethrower AFV", "UCA---"),
    108: ("armhq", "Armoured HQ", "UCA---"),
    200: ("artillery", "Artillery", "UCF---"),
    201: ("antitank", "Anti-Tank", "UCAA--"),
    202: ("spat", "SP AT", "UCAA--"),
    203: ("mortar", "Mortar", "UCFM--"),
    204: ("spmortar", "SP Mortar", "UCFM--"),
    205: ("howitzer", "Howitzer", "UCFH--"),
    206: ("sphowitzer", "SP Howitzer", "UCFH--"),
    207: ("gun", "Gun", "UCF---"),
    208: ("spgun", "SP Gun", "UCF---"),
    209: ("infgun", "Inf Gun", "UCF---"),
    210: ("spinfgun", "SP Inf Gun", "UCF---"),
    211: ("rl", "Rocket Launcher", "UCFR--"),
    212: ("sprl", "SP RL", "UCFR--"),
    213: ("flak", "Flak", "UCD---"),
    214: ("spflak", "SP Flak", "UCD---"),
    215: ("mothowitzer", "Mot Howitzer", "UCFH--"),
    216: ("motmortar", "Mot Mortar", "UCFM--"),
    217: ("motgun", "Mot Gun", "UCF---"),
    218: ("motinfgun", "Mot Inf Gun", "UCF---"),
    219: ("motrl", "Mot RL", "UCFR--"),
    220: ("motflak", "Mot Flak", "UCD---"),
    221: ("motat", "Mot AT", "UCAA--"),
    222: ("abnarty", "Abn Arty", "UCF---"),
    223: ("paraarty", "Para Arty", "UCF---"),
}
# XML sub-type text -> code (for .xml establishment exports)
_SUB_BY_NAME = {v[1].lower(): k for k, v in ESTAB_SUBTYPES.items()}

ESTAB_SIZES = {0: "army-group", 1: "army", 2: "corps", 3: "division", 4: "brigade",
               5: "battalion", 6: "company", 7: "platoon", 8: "section"}
SIZE_ECHELON = {"army-group": "L", "army": "K", "corps": "J", "division": "I",
                "brigade": "H", "regiment": "G", "battalion": "F", "company": "E",
                "platoon": "D", "section": "C"}

ESTAB_PICTURES = {0: "tank", 1: "assault-gun", 2: "light-tank", 3: "armoured-car",
                  4: "artillery", 5: "at-gun", 6: "heavy-flak", 7: "light-flak",
                  8: "rockets", 9: "sp-artillery", 10: "engineer", 11: "bridging",
                  12: "mech-inf", 13: "motor-inf", 14: "infantry", 15: "para",
                  16: "hq", 17: "hmg", 18: "mortar", 19: "base", 23: "heavy-tank",
                  24: "inf-gun", 26: "motorcycle"}
# For HQs the sub-type only says "HQ"; the counter picture says what kind.
_PICTURE_FUNCTION = {"tank": "UCA---", "light-tank": "UCA---", "heavy-tank": "UCA---",
                     "assault-gun": "UCA---", "armoured-car": "UCAW--",
                     "artillery": "UCF---", "sp-artillery": "UCF---", "rockets": "UCFR--",
                     "at-gun": "UCAA--", "heavy-flak": "UCD---", "light-flak": "UCD---",
                     "engineer": "UCE---", "bridging": "UCE---", "mech-inf": "UCIZ--",
                     "motor-inf": "UCIM--", "infantry": "UCI---", "para": "UCIA--",
                     "hmg": "UCI---", "mortar": "UCFM--", "base": "USS---",
                     "inf-gun": "UCF---", "motorcycle": "UCR---", "hq": "UCI---"}


def estab_function(e):
    f = ESTAB_SUBTYPES.get(e["sub_code"], (None, None, None))[2]
    if f is None:
        f = _PICTURE_FUNCTION.get(e["picture"], "UCI---")
    return f


class Estab:
    """Establishment database: force id -> dict(name, type, sub, size, hq, ...)."""

    def __init__(self, path):
        self.path = path
        if path.lower().endswith(".xml"):
            self.forces = self._load_xml(path)
        else:
            self.forces = self._load_coe(path)
        if not self.forces:
            raise CogError("No unit establishments found in this file")

    @staticmethod
    def _entry(fid, name, type_name, sub_code, sub_name, size, hq, picture):
        key_sub = ESTAB_SUBTYPES.get(sub_code, (None,))[0] if sub_code is not None else None
        key_sub = key_sub or re.sub(r"[^a-z]", "", (sub_name or "").lower())
        return dict(id=fid, name=name, type=type_name, sub_code=sub_code,
                    sub=sub_name, size=size, hq=hq, picture=picture,
                    key=f"{type_name},{key_sub}")

    def _load_coe(self, path):
        with open(path, "rb") as f:
            raw = f.read()
        if raw[:4] != b"POD\x00":
            raise CogError("Not a Command Ops establishment file: missing POD header")
        holder = CogFile.__new__(CogFile)
        holder.raw = raw
        objs = holder._load_objects()
        forces = {}
        for (cls, fid), b in objs.items():
            if cls != CLS_FORCE:
                continue
            try:
                n = _u32(b, 0)
                if not 0 < n < 300:
                    continue
                name = b[4:4 + n].decode("latin-1")
                o = 4 + n
                o += 4 + _u32(b, o)
                f = b[o:o + 40]
                if len(f) < 33 or f[29] > 3 or f[28] > 1:
                    continue
                sub = f[30]
                forces[fid] = self._entry(
                    fid, name, ESTAB_TYPES[f[29]], sub,
                    ESTAB_SUBTYPES.get(sub, (None, f"Sub-type {sub}"))[1],
                    ESTAB_SIZES.get(f[32], ""), bool(f[28]),
                    ESTAB_PICTURES.get(f[27], ""))
            except (struct.error, IndexError, KeyError):
                continue
        return forces

    def _load_xml(self, path):
        import xml.etree.ElementTree as ET
        forces = {}
        for f in ET.parse(path).getroot().iter("force"):
            try:
                fid = int(f.get("id"))
            except (TypeError, ValueError):
                continue
            icon = f.find("icon")
            sub_name = (f.findtext("sub-type") or "").strip()
            forces[fid] = self._entry(
                fid, (f.findtext("name") or "").strip(), (f.findtext("type") or "").strip(),
                _SUB_BY_NAME.get(sub_name.lower()), sub_name,
                (f.findtext("size") or "").strip(),
                (icon is not None and (icon.findtext("is-hq") or "").strip() == "yes"),
                (icon.findtext("picture-symbol") or "").strip() if icon is not None else "")
        return forces


def find_estab(cog, extra_dirs=()):
    """Look for the save's establishment file near the save and in given folders."""
    return find_game_file(cog, cog.estab_name, extra_dirs, alt_ext=".xml")


def find_game_file(cog, name, extra_dirs=(), alt_ext=None):
    """Search for a game data file (e.g. COTAEstab.coe, Elasson.cop) near the save
    (the save folder and up to two levels up, e.g. the game folder) and in extra_dirs."""
    name = (name or "").lower()
    if not name:
        return None
    stem = os.path.splitext(name)[0]
    start = os.path.dirname(os.path.abspath(cog.path))
    roots = list(extra_dirs) + [start, os.path.dirname(start), os.path.dirname(os.path.dirname(start))]
    seen = set()
    for root in roots:
        if not root or root in seen or not os.path.isdir(root):
            continue
        seen.add(root)
        for dirpath, dirnames, files in os.walk(root):
            if dirpath[len(root):].count(os.sep) >= 3:
                dirnames[:] = []
            for fn in files:
                low = fn.lower()
                if low == name or low.endswith("-" + name):
                    return os.path.join(dirpath, fn)
            if alt_ext:
                for fn in files:
                    low = fn.lower()
                    if low == stem + alt_ext or low.endswith("-" + stem + alt_ext):
                        return os.path.join(dirpath, fn)
    return None


class MapFile:
    """The scenario map (.cop), decoded:
      size in metres; a terrain grid (normally 100 m cells) holding elevation in
      metres and feature bits; vector areas (woods, orchards, towns...) and lines
      (rivers, tracks, roads, bridges...); and the place names printed on the map.
    Vector x coordinates are stored at half-metre resolution (detected and halved)."""

    CLS_MAP, CLS_AREA_TYPE, CLS_POLYGON, CLS_POLYLINE, CLS_LINE_TYPE, CLS_LABEL = 28, 32, 30, 34, 35, 38

    def __init__(self, path):
        self.path = path
        with open(path, "rb") as f:
            raw = f.read()
        if raw[:4] != b"POD\x00":
            raise CogError("Not a Command Ops map file")
        holder = CogFile.__new__(CogFile)
        holder.raw = raw
        objs = holder._load_objects()
        self.name, self.width, self.height = "", 0, 0
        self.cell, self.gw, self.gh, self.elev = 100, 0, 0, None
        for (cls, _i), b in objs.items():
            if cls == self.CLS_MAP:
                self._read_map(b)
        self.places = {}
        for (cls, _i), b in sorted(objs.items()):
            if cls != self.CLS_LABEL:
                continue
            try:
                n = _u32(b, 8)
                nm = b[12:12 + n].decode("latin-1").strip()
                x, y = _u32(b, 12 + n), _u32(b, 16 + n)
            except (struct.error, IndexError):
                continue
            if nm and "contour" not in nm.lower() and 0 <= x <= 200000 and 0 <= y <= 200000:
                self.places.setdefault(nm, (x, y))
        self.areas = self._features(objs, self.CLS_AREA_TYPE)    # [(type name, [(x,y)...])]
        self.lines = self._features(objs, self.CLS_LINE_TYPE)
        allx = [x for _n, p in self.areas + self.lines for x, _y in p]
        if allx and self.width and max(allx) > self.width * 1.5:
            self.areas = [(n, [(x / 2, y) for x, y in p]) for n, p in self.areas]
            self.lines = [(n, [(x / 2, y) for x, y in p]) for n, p in self.lines]

    def _read_map(self, b):
        n = _u32(b, 0x61)
        if not 0 < n < 100:
            return
        self.name = b[0x65:0x65 + n].decode("latin-1")
        self.width, self.height = _u32(b, 0x65 + n + 4), _u32(b, 0x65 + n + 8)
        for cell in (100, 50, 200, 250, 25):
            gw, gh = -(-self.width // cell), -(-self.height // cell)
            i = b.find(struct.pack("<II", cell, gw * gh))
            if i < 0:
                continue
            best = None
            for gap in range(0, 8):     # find the byte offset of the grid
                start = i + 8 + gap
                if start + 8 * gw * gh > len(b):
                    continue
                vals = struct.unpack_from(f"<{2 * gw * gh}I", b, start)
                el = [(vals[2 * k + 1] & 0xFF) + 256 * ((vals[2 * k] >> 4) & 7) for k in range(gw * gh)]
                n = min(len(el) - 1, 20000)
                rough = sum(abs(el[k + 1] - el[k]) for k in range(n)) / n + 0.5
                mean = sum(el[:n]) / n
                spread = (sum((e - mean) ** 2 for e in el[:n]) / n) ** 0.5
                score = spread / rough      # real terrain: wide range, smooth steps
                if best is None or score > best[0]:
                    best = (score, rough, el)
            if best and best[1] < 60:
                self.cell, self.gw, self.gh, self.elev = cell, gw, gh, best[2]
                return

    @staticmethod
    def _features(objs, type_cls):
        out = []
        for (cls, _i), b in sorted(objs.items()):
            if cls != type_cls:
                continue
            m = re.search(rb"[A-Za-z][ -~]{2,}", b)
            if not m:
                continue
            name = m.group().decode("latin-1")
            try:
                n = _u32(b, 8)
                for j in range(min(n, 100000)):
                    rc, rid = struct.unpack_from("<II", b, 12 + 8 * j)
                    pb = objs.get((rc, rid))
                    if not pb:
                        continue
                    k = _u32(pb, 8)
                    pts = [struct.unpack_from("<ii", pb, 12 + 8 * q) for q in range(k)
                           if 20 + 8 * q <= len(pb)]
                    if len(pts) >= 2:
                        out.append((name, pts))
            except struct.error:
                continue
        return out


# --------------------------------------------------------------------------
# Finding the game installation (read-only lookups, no disk scanning)
# --------------------------------------------------------------------------

GAME_EXE = "cmdops.exe"


def _has_exe(folder):
    try:
        return folder and os.path.isdir(folder) and any(
            f.lower() == GAME_EXE for f in os.listdir(folder))
    except OSError:
        return False


def _steam_roots():
    roots = []
    if sys.platform == "win32":
        try:
            import winreg
            for hive, key, val in ((winreg.HKEY_CURRENT_USER, r"Software\Valve\Steam", "SteamPath"),
                                   (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\WOW6432Node\Valve\Steam", "InstallPath"),
                                   (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Valve\Steam", "InstallPath")):
                try:
                    with winreg.OpenKey(hive, key) as k:
                        roots.append(winreg.QueryValueEx(k, val)[0])
                except OSError:
                    pass
        except ImportError:
            pass
        for env in ("ProgramFiles(x86)", "ProgramFiles"):
            if os.environ.get(env):
                roots.append(os.path.join(os.environ[env], "Steam"))
    else:
        home = os.path.expanduser("~")
        roots += [os.path.join(home, ".steam", "steam"), os.path.join(home, ".local", "share", "Steam"),
                  os.path.join(home, "Library", "Application Support", "Steam")]
    libs = []
    for r in roots:
        if not r or not os.path.isdir(r):
            continue
        libs.append(r)
        vdf = os.path.join(r, "steamapps", "libraryfolders.vdf")
        try:
            with open(vdf, "r", encoding="utf-8", errors="ignore") as f:
                libs += [p.replace("\\\\", "\\") for p in re.findall(r'"path"\s+"([^"]+)"', f.read())]
        except OSError:
            pass
    seen, out = set(), []
    for l in libs:
        key = os.path.normcase(os.path.normpath(l))
        if key not in seen:
            seen.add(key)
            out.append(l)
    return out


def _uninstall_locations():
    out = []
    if sys.platform != "win32":
        return out
    try:
        import winreg
    except ImportError:
        return out
    for hive in (winreg.HKEY_LOCAL_MACHINE, winreg.HKEY_CURRENT_USER):
        for base in (r"SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall",
                     r"SOFTWARE\WOW6432Node\Microsoft\Windows\CurrentVersion\Uninstall"):
            try:
                with winreg.OpenKey(hive, base) as k:
                    for i in range(winreg.QueryInfoKey(k)[0]):
                        try:
                            with winreg.OpenKey(k, winreg.EnumKey(k, i)) as sk:
                                name = winreg.QueryValueEx(sk, "DisplayName")[0]
                                if "command ops" in str(name).lower():
                                    out.append(winreg.QueryValueEx(sk, "InstallLocation")[0])
                        except OSError:
                            continue
            except OSError:
                continue
    return out


def find_game_install(hint_paths=()):
    """Return the Command Ops 2 folder (the one holding CmdOps.exe), or None.
    Looks only at: given hints and their parents, Steam libraries (registry +
    libraryfolders.vdf), uninstall entries, and the usual install folders."""
    cands = []
    for h in hint_paths:
        if not h:
            continue
        p = os.path.abspath(h)
        if os.path.isfile(p):
            p = os.path.dirname(p)
        for _ in range(4):
            cands.append(p)
            p = os.path.dirname(p)
    for lib in _steam_roots():
        common = os.path.join(lib, "steamapps", "common")
        cands.append(os.path.join(common, "Command Ops 2"))
        try:
            cands += [os.path.join(common, d) for d in os.listdir(common) if "command ops" in d.lower()]
        except OSError:
            pass
    cands += _uninstall_locations()
    for env in ("ProgramFiles(x86)", "ProgramFiles"):
        pf = os.environ.get(env)
        if pf:
            for vendor in ("Matrix Games", "Slitherine", "Panther Games", ""):
                cands.append(os.path.join(pf, vendor, "Command Ops 2"))
    for c in cands:
        if _has_exe(c):
            return c
    return None


def find_in_install(base, filename, subdirs=()):
    """Find filename (case-insensitive) under base, preferring the given subfolders."""
    if not base or not filename:
        return None
    low = filename.lower()
    for sd in list(subdirs) + [""]:
        d = os.path.join(base, sd) if sd else base
        try:
            for f in os.listdir(d):
                if f.lower() == low:
                    return os.path.join(d, f)
        except OSError:
            continue
    for dirpath, dirnames, files in os.walk(base):
        if dirpath[len(base):].count(os.sep) >= 3:
            dirnames[:] = []
        for f in files:
            if f.lower() == low:
                return os.path.join(dirpath, f)
    return None


# --------------------------------------------------------------------------
# Map rendering (Pillow)
# --------------------------------------------------------------------------

AREA_STYLE = {  # name: (RGB, alpha 0-255)
    "Woods": ((63, 122, 58), 140), "Light Woods": ((127, 174, 99), 115), "OrchardsS": ((181, 201, 106), 115),
    "Orchards": ((181, 201, 106), 115), "Village": ((176, 65, 62), 205), "Town": ((140, 45, 42), 215),
    "City": ((110, 31, 29), 230), "Factory": ((85, 85, 85), 205), "Industrial": ((85, 85, 85), 205),
    "Marsh": ((127, 179, 201), 130), "Major Water Obstacle": ((79, 143, 192), 205),
    "Sea": ((79, 143, 192), 230), "BrokenM": ((138, 117, 96), 90), "Fort or Church": ((0, 0, 0), 205),
    "Airfield": ((153, 153, 153), 150), "Beach": ((235, 220, 170), 160)}
LINE_STYLE = {  # name: (RGB, width in metres, dashed)
    "River Bed": ((47, 111, 176), 45, False), "Creek Bed": ((91, 152, 207), 25, False),
    "Track": ((122, 82, 48), 14, True), "Minor Road": ((176, 106, 42), 28, False),
    "Road": ((208, 53, 43), 38, False), "Highway": ((196, 22, 28), 60, False),
    "Rail": ((34, 34, 34), 30, True), "Rail Bridge": ((0, 0, 0), 80, False),
    "Lt Bridge": ((0, 0, 0), 70, False), "Med Bridge": ((0, 0, 0), 80, False),
    "Hvy Bridge": ((0, 0, 0), 95, False), "Ferry or Ford": ((27, 79, 138), 80, False),
    "Crossing Point": ((0, 0, 0), 70, False), "Breakwater": ((60, 60, 60), 40, False)}
FRIENDLY_FILL, HOSTILE_FILL = (128, 224, 255), (255, 128, 128)


def _font(size, bold=False):
    from PIL import ImageFont
    names = (["arialbd.ttf", "DejaVuSans-Bold.ttf"] if bold else []) + ["arial.ttf", "DejaVuSans.ttf"]
    for n in names:
        try:
            return ImageFont.truetype(n, size)
        except OSError:
            continue
    try:
        return ImageFont.load_default(size)
    except TypeError:
        return ImageFont.load_default()


def render_terrain(mapf, width_m, height_m, ppm):
    """Background image (RGB) of the map at ppm pixels per metre."""
    from PIL import Image, ImageDraw
    W, H = max(1, int(width_m * ppm)), max(1, int(height_m * ppm))
    if mapf is not None and mapf.elev:
        gw, gh, cell, el = mapf.gw, mapf.gh, mapf.cell, mapf.elev
        stops = [(0, (201, 223, 178)), (150, (232, 226, 176)), (350, (217, 192, 142)),
                 (600, (196, 154, 108)), (850, (163, 123, 90)), (1100, (242, 239, 233))]

        def colour(e):
            for (e0, c0), (e1, c1) in zip(stops, stops[1:]):
                if e <= e1:
                    t = max(0.0, (e - e0) / (e1 - e0))
                    return tuple(int(c0[i] + (c1[i] - c0[i]) * t) for i in range(3))
            return stops[-1][1]
        az, alt = math.radians(315), math.radians(45)
        px = bytearray()
        for r in range(gh):
            for q in range(gw):
                e = el[r * gw + q]
                dzdx = (el[r * gw + min(q + 1, gw - 1)] - el[r * gw + max(q - 1, 0)]) / (2 * cell)
                dzdy = (el[min(r + 1, gh - 1) * gw + q] - el[max(r - 1, 0) * gw + q]) / (2 * cell)
                slope = math.atan(2.5 * math.hypot(dzdx, dzdy))
                aspect = math.atan2(dzdy, -dzdx)
                shade = (math.sin(alt) * math.cos(slope) +
                         math.cos(alt) * math.sin(slope) * math.cos(az - aspect))
                k = 0.55 + 0.5 * max(0.0, shade)
                px += bytes(min(255, int(ch * k)) for ch in colour(e))
        img = Image.frombytes("RGB", (gw, gh), bytes(px))
        img = img.resize((int(gw * cell * ppm), int(gh * cell * ppm)), Image.BICUBIC).crop((0, 0, W, H))
    else:
        img = Image.new("RGB", (W, H), (236, 232, 214))
    if mapf is None:
        d = ImageDraw.Draw(img)
        step = 1000 * ppm
        for k in range(int(W / step) + 1):
            d.line([(k * step, 0), (k * step, H)], fill=(215, 210, 190))
        for k in range(int(H / step) + 1):
            d.line([(0, k * step), (W, k * step)], fill=(215, 210, 190))
        return img
    over = Image.new("RGBA", img.size, (0, 0, 0, 0))
    d = ImageDraw.Draw(over)
    order = ["BrokenM", "Marsh", "Beach", "Sea", "Major Water Obstacle", "Light Woods", "OrchardsS",
             "Orchards", "Woods", "Airfield", "Village", "Town", "City", "Industrial", "Factory",
             "Fort or Church"]
    for nm in order:
        col, a = AREA_STYLE[nm]
        for name, pts in mapf.areas:
            if name == nm and len(pts) >= 3:
                d.polygon([(x * ppm, y * ppm) for x, y in pts], fill=col + (a,))
    img = Image.alpha_composite(img.convert("RGBA"), over)
    d = ImageDraw.Draw(img)
    for nm in ["Creek Bed", "River Bed", "Track", "Minor Road", "Road", "Highway", "Rail",
               "Ferry or Ford", "Lt Bridge", "Med Bridge", "Hvy Bridge", "Rail Bridge", "Crossing Point"]:
        if nm not in LINE_STYLE:
            continue
        col, wm, dashed = LINE_STYLE[nm]
        w = max(1, int(round(wm * ppm)))
        for name, pts in mapf.lines:
            if name != nm:
                continue
            xy = [(x * ppm, y * ppm) for x, y in pts]
            if dashed:
                for a, b in zip(xy, xy[1:]):
                    seg = math.dist(a, b)
                    n = max(1, int(seg / (w * 4)))
                    for s in range(0, n, 2):
                        t0, t1 = s / n, min(1, (s + 1) / n)
                        d.line([(a[0] + (b[0] - a[0]) * t0, a[1] + (b[1] - a[1]) * t0),
                                (a[0] + (b[0] - a[0]) * t1, a[1] + (b[1] - a[1]) * t1)], fill=col, width=w)
            else:
                d.line(xy, fill=col, width=w, joint="curve")
    f = _font(max(9, int(170 * ppm)))
    for nm, (x, y) in mapf.places.items():
        d.text((x * ppm, y * ppm), nm, font=f, fill=(30, 30, 30), anchor="lm",
               stroke_width=max(1, int(25 * ppm)), stroke_fill=(255, 255, 255))
    return img.convert("RGB")


def _dashed(d, pts, fill, width, dash):
    for a, b in zip(pts, pts[1:]):
        seg = math.dist(a, b)
        n = max(1, int(seg / dash))
        for k in range(0, n, 2):
            t0, t1 = k / n, min(1.0, (k + 1) / n)
            d.line([(a[0] + (b[0] - a[0]) * t0, a[1] + (b[1] - a[1]) * t0),
                    (a[0] + (b[0] - a[0]) * t1, a[1] + (b[1] - a[1]) * t1)], fill=fill, width=width)


def draw_unit(d, cx, cy, sidc, label, size, font, ech_font, stale=False):
    """A simple MIL-STD-2525 style ground unit symbol centred at cx, cy.
    stale=True (last known position) draws a dashed, paler frame."""
    hostile = sidc[1] == "H"
    w, h = size, size * 0.66
    fill = HOSTILE_FILL if hostile else FRIENDLY_FILL
    if stale:
        fill = tuple(int(c + (255 - c) * 0.6) for c in fill)
    ln = max(1, int(size / 14))
    if hostile:
        r = h * 0.95
        box = (cx - r, cy - r, cx + r, cy + r)
        diamond = [(cx, cy - r), (cx + r, cy), (cx, cy + r), (cx - r, cy)]
        if stale:
            d.polygon(diamond, fill=fill)
            _dashed(d, diamond + [diamond[0]], (0, 0, 0), ln, size / 7)
        else:
            d.polygon(diamond, fill=fill, outline=(0, 0, 0), width=ln)
        x0, y0, x1, y1 = cx - r * 0.5, cy - r * 0.5, cx + r * 0.5, cy + r * 0.5
        top = cy - r
    else:
        box = (cx - w / 2, cy - h / 2, cx + w / 2, cy + h / 2)
        if stale:
            d.rectangle(box, fill=fill)
            rect = [(box[0], box[1]), (box[2], box[1]), (box[2], box[3]), (box[0], box[3]), (box[0], box[1])]
            _dashed(d, rect, (0, 0, 0), ln, size / 7)
        else:
            d.rectangle(box, fill=fill, outline=(0, 0, 0), width=ln)
        x0, y0, x1, y1 = box
        top = y0
    func = sidc[4:10]
    k = (0, 0, 0)
    if func.startswith("UCI") or func.startswith("UCEC"):
        d.line([(x0, y0), (x1, y1)], fill=k, width=ln)
        d.line([(x0, y1), (x1, y0)], fill=k, width=ln)
    if func.startswith("UCA") and not func.startswith("UCAA") and not func.startswith("UCAW"):
        d.ellipse((x0 + (x1 - x0) * 0.18, y0 + (y1 - y0) * 0.22, x1 - (x1 - x0) * 0.18, y1 - (y1 - y0) * 0.22),
                  outline=k, width=ln)
    if func.startswith("UCAW") or func.startswith("UCR"):
        d.line([(x0, y1), (x1, y0)], fill=k, width=ln)
    if func.startswith("UCAA"):
        d.line([(x0, y1), ((x0 + x1) / 2, y0), (x1, y1)], fill=k, width=ln)
    if func.startswith("UCF"):
        r = (y1 - y0) * 0.16
        mx, my = (x0 + x1) / 2, (y0 + y1) / 2
        if func.startswith("UCFM"):
            d.ellipse((mx - r, my - r, mx + r, my + r), outline=k, width=ln)
            d.line([(mx, my - r), (mx, y0 + (y1 - y0) * 0.1)], fill=k, width=ln)
        else:
            d.ellipse((mx - r, my - r, mx + r, my + r), fill=k)
    if func.startswith("UCE") and not func.startswith("UCEC"):
        my = (y0 + y1) / 2
        d.line([(x0 + (x1 - x0) * 0.25, my), (x1 - (x1 - x0) * 0.25, my)], fill=k, width=ln)
        for fx in (0.25, 0.5, 0.75):
            d.line([(x0 + (x1 - x0) * fx, my), (x0 + (x1 - x0) * fx, my + (y1 - y0) * 0.22)], fill=k, width=ln)
    if func.startswith("UCD"):
        d.arc((x0 + (x1 - x0) * 0.2, y0 + (y1 - y0) * 0.35, x1 - (x1 - x0) * 0.2, y1 + (y1 - y0) * 0.45),
              180, 360, fill=k, width=ln)
    if func.startswith("US"):
        d.line([(x0, y1 - (y1 - y0) * 0.25), (x1, y1 - (y1 - y0) * 0.25)], fill=k, width=ln)
    if sidc[10] == "A":                                  # headquarters staff
        d.line([(box[0], cy), (box[0], box[3] + h * 0.7)], fill=k, width=ln)
    ech = {"C": "••", "D": "•••", "E": "|", "F": "||", "G": "|||", "H": "X", "I": "XX",
           "J": "XXX", "K": "XXXX", "L": "XXXXX"}.get(sidc[11], "")
    if ech:
        d.text((cx, top - 1), ech, font=ech_font, fill=k, anchor="mb")
    if label:
        d.text((box[2] + size * 0.15, cy), label, font=font, fill=(10, 10, 10), anchor="lm",
               stroke_width=max(1, int(size / 12)), stroke_fill=(255, 255, 255))


def draw_orders(d, ppm, items, size, font):
    """Orders on the map: arrows for moves/attacks/withdrawals, rings for defend/rest
    areas, crosshairs for fire targets."""
    for it in items:
        col = (25, 70, 200) if it["friendly"] else (200, 30, 30)
        pts = [(x * ppm, y * ppm) for x, y in it["pts"]]
        w = max(2, size // 9)
        if it["kind"] == "arrow":
            tip, tail = (pts[0], pts[1]) if ARROW_TIP_FIRST else (pts[1], pts[0])
            ang = math.atan2(tip[1] - tail[1], tip[0] - tail[0])
            head = size * 0.55
            dash = it["type"] in ("Move", "Exit", "Probe", "Construct Bridge")
            if dash:
                _dashed(d, [tail, tip], col, w, size / 3)
            else:
                d.line([tail, tip], fill=col, width=w)
            left = (tip[0] - head * math.cos(ang - 0.45), tip[1] - head * math.sin(ang - 0.45))
            right = (tip[0] - head * math.cos(ang + 0.45), tip[1] - head * math.sin(ang + 0.45))
            d.polygon([tip, left, right], fill=col)
            if it["type"] in ("Withdraw", "Delay"):
                mid = ((tip[0] + tail[0]) / 2, (tip[1] + tail[1]) / 2)
                d.text(mid, "W" if it["type"] == "Withdraw" else "D", font=font, fill=col, anchor="mm",
                       stroke_width=max(1, size // 12), stroke_fill=(255, 255, 255))
        elif it["kind"] == "area":
            _dashed(d, pts + [pts[0]], col, w, size / 4) if it["type"] in ("Rest", "Reorg") else \
                d.line(pts + [pts[0]], fill=col, width=w)
        else:
            (x, y), r = pts[0], size * 0.45
            d.ellipse((x - r, y - r, x + r, y + r), outline=col, width=w)
            d.line([(x - r * 1.6, y), (x + r * 1.6, y)], fill=col, width=w)
            d.line([(x, y - r * 1.6), (x, y + r * 1.6)], fill=col, width=w)


def draw_star(d, x, y, r, fill):
    pts = []
    for i in range(10):
        a = math.pi / 2 + i * math.pi / 5
        rr = r if i % 2 == 0 else r * 0.45
        pts.append((x + rr * math.cos(a), y - rr * math.sin(a)))
    d.polygon(pts, fill=fill, outline=(0, 0, 0))


def render_scene(base_img, ppm, cog, friendly_side, show_enemy="fog", refs=(), title="", show_orders=True):
    """Units, objectives, reference markers (and a title bar) on top of base_img."""
    from PIL import Image, ImageDraw
    img = base_img.copy().convert("RGB")
    d = ImageDraw.Draw(img)
    size = max(12, int(260 * ppm))
    f, fe, fo = _font(max(8, int(size * 0.42))), _font(max(7, int(size * 0.38)), True), _font(max(8, int(size * 0.45)), True)
    for o in cog.objectives:
        if o["ai"]:
            continue
        draw_star(d, o["x"] * ppm, o["y"] * ppm, size * 0.45, (255, 205, 40))
    if show_orders:
        draw_orders(d, ppm, order_items(cog, friendly_side, include_enemy=(_enemy_mode(show_enemy) == "all")),
                    size, fo)
    for su in shown_units(cog, friendly_side, show_enemy):
        label = su["T"]
        if not su["friendly"] and _enemy_mode(show_enemy) == "fog":
            bits = [b for b in ((f"{su['conf']}%" if su.get("conf") is not None else ""), su.get("seen", "")) if b]
            if bits:
                label += " · " + " ".join(bits)
        draw_unit(d, su["x"] * ppm, su["y"] * ppm, su["sidc"], label, size, f, fe, stale=su["stale"])
    seen = set()
    for o in cog.objectives:
        if o["ai"] or o["name"] in seen:
            continue
        seen.add(o["name"])
        d.text((o["x"] * ppm + size * 0.5, o["y"] * ppm + size * 0.45), o["name"], font=fo, fill=(90, 60, 0),
               anchor="lt", stroke_width=max(1, size // 12), stroke_fill=(255, 255, 255))
    for i, r in enumerate(refs):
        x, y = r["xy"][0] * ppm, r["xy"][1] * ppm
        rr = size * 0.6
        d.ellipse((x - rr, y - rr, x + rr, y + rr), outline=(200, 0, 160), width=max(2, size // 8))
        d.line([(x - rr * 1.5, y), (x + rr * 1.5, y)], fill=(200, 0, 160), width=max(1, size // 12))
        d.line([(x, y - rr * 1.5), (x, y + rr * 1.5)], fill=(200, 0, 160), width=max(1, size // 12))
        d.text((x + rr * 1.2, y - rr * 1.2), f"{i + 1}: {r['ll'][0]:.4f}, {r['ll'][1]:.4f}", font=fo,
               fill=(200, 0, 160), anchor="lb", stroke_width=max(1, size // 12), stroke_fill=(255, 255, 255))
    if title:
        bar = int(size * 1.3)
        out = Image.new("RGB", (img.width, img.height + bar), (34, 34, 34))
        out.paste(img, (0, bar))
        ImageDraw.Draw(out).text((size * 0.5, bar / 2), title, font=_font(int(bar * 0.5), True),
                                 fill=(255, 255, 255), anchor="lm")
        return out
    return img


# --------------------------------------------------------------------------
# Georeferencing
# --------------------------------------------------------------------------
#
# How Panther Games' GameStatExporter.exe does it (from its disassembly and the
# gdal202.dll it links): the two reference lat/lons are projected with GDAL into
# a projected CRS (option --epsg, default 3857 = Web Mercator; GDAL hands the
# maths to PROJ via pj_transform). Each game coordinate is then interpolated
# separately per axis between the two references:
#     X = P1x + (x - x1) / (x2 - x1) * (P2x - P1x)
#     Y = P1y + (y - y1) / (y2 - y1) * (P2y - P1y)
# and the point is transformed back to WGS84 (EPSG:4326).
# This module reproduces that exactly (model "axis" + Web Mercator) and adds a
# uniform-scale-plus-rotation model, least squares for 3+ points, and checks.

R_EARTH = 6378137.0              # WGS84 semi-major axis (also the 3857 sphere)
WGS84_F = 1 / 298.257223563
R_MEAN = 6371008.8               # for great-circle distances


def haversine(lat1, lon1, lat2, lon2):
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp, dl = p2 - p1, math.radians(lon2 - lon1)
    h = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * R_MEAN * math.asin(min(1.0, math.sqrt(h)))


class WebMercator:
    """EPSG:3857 exactly as PROJ computes it (+proj=merc +a=+b=6378137)."""
    name = "Web Mercator (EPSG:3857)"
    code = "3857"

    def forward(self, lat, lon):
        lat = max(-85.0511287798, min(85.0511287798, lat))
        return (R_EARTH * math.radians(lon),
                R_EARTH * math.log(math.tan(math.pi / 4 + math.radians(lat) / 2)))

    def inverse(self, x, y):
        return (math.degrees(2 * math.atan(math.exp(y / R_EARTH)) - math.pi / 2),
                math.degrees(x / R_EARTH))


class TransverseMercator:
    """UTM / transverse Mercator on WGS84 using Krüger's series to n^6
    (the algorithm PROJ uses for +proj=utm / +proj=tmerc). Sub-millimetre."""

    def __init__(self, lon0, k0=0.9996, fe=500000.0, fn=0.0, name="", code=""):
        self.lon0, self.k0, self.fe, self.fn = lon0, k0, fe, fn
        self.name, self.code = name, code
        n = WGS84_F / (2 - WGS84_F)
        self.n = n
        self.A = R_EARTH / (1 + n) * (1 + n**2 / 4 + n**4 / 64 + n**6 / 256)
        self.alpha = [
            n/2 - 2*n**2/3 + 5*n**3/16 + 41*n**4/180 - 127*n**5/288 + 7891*n**6/37800,
            13*n**2/48 - 3*n**3/5 + 557*n**4/1440 + 281*n**5/630 - 1983433*n**6/1935360,
            61*n**3/240 - 103*n**4/140 + 15061*n**5/26880 + 167603*n**6/181440,
            49561*n**4/161280 - 179*n**5/168 + 6601661*n**6/7257600,
            34729*n**5/80640 - 3418889*n**6/1995840,
            212378941*n**6/319334400]
        self.beta = [
            n/2 - 2*n**2/3 + 37*n**3/96 - n**4/360 - 81*n**5/512 + 96199*n**6/604800,
            n**2/48 + n**3/15 - 437*n**4/1440 + 46*n**5/105 - 1118711*n**6/3870720,
            17*n**3/480 - 37*n**4/840 - 209*n**5/4480 + 5569*n**6/90720,
            4397*n**4/161280 - 11*n**5/504 - 830251*n**6/7257600,
            4583*n**5/161280 - 108847*n**6/3991680,
            20648693*n**6/638668800]
        self.delta = [
            2*n - 2*n**2/3 - 2*n**3 + 116*n**4/45 + 26*n**5/45 - 2854*n**6/675,
            7*n**2/3 - 8*n**3/5 - 227*n**4/45 + 2704*n**5/315 + 2323*n**6/945,
            56*n**3/15 - 136*n**4/35 - 1262*n**5/105 + 73814*n**6/2835,
            4279*n**4/630 - 332*n**5/35 - 399572*n**6/14175,
            4174*n**5/315 - 144838*n**6/6237,
            601676*n**6/22275]

    @classmethod
    def utm_for(cls, lat, lon):
        zone = int((lon + 180) // 6) + 1
        south = lat < 0
        epsg = (32700 if south else 32600) + zone
        return cls(zone * 6 - 183, fn=10000000.0 if south else 0.0,
                   name=f"UTM zone {zone}{'S' if south else 'N'} (EPSG:{epsg})", code=str(epsg))

    def forward(self, lat, lon):
        n = self.n
        phi, lam = math.radians(lat), math.radians(lon - self.lon0)
        c = 2 * math.sqrt(n) / (1 + n)
        t = math.sinh(math.atanh(math.sin(phi)) - c * math.atanh(c * math.sin(phi)))
        xi_ = math.atan2(t, math.cos(lam))
        eta_ = math.atanh(math.sin(lam) / math.sqrt(1 + t * t))
        xi, eta = xi_, eta_
        for j, a in enumerate(self.alpha, 1):
            xi += a * math.sin(2 * j * xi_) * math.cosh(2 * j * eta_)
            eta += a * math.cos(2 * j * xi_) * math.sinh(2 * j * eta_)
        return self.fe + self.k0 * self.A * eta, self.fn + self.k0 * self.A * xi

    def inverse(self, x, y):
        xi = (y - self.fn) / (self.k0 * self.A)
        eta = (x - self.fe) / (self.k0 * self.A)
        xi_, eta_ = xi, eta
        for j, b in enumerate(self.beta, 1):
            xi_ -= b * math.sin(2 * j * xi) * math.cosh(2 * j * eta)
            eta_ -= b * math.cos(2 * j * xi) * math.sinh(2 * j * eta)
        chi = math.asin(math.sin(xi_) / math.cosh(eta_))
        phi = chi + sum(d * math.sin(2 * j * chi) for j, d in enumerate(self.delta, 1))
        lam = math.atan2(math.sinh(eta_), math.cos(xi_))
        return math.degrees(phi), self.lon0 + math.degrees(lam)


class PyprojProjection:
    """Any EPSG code, through pyproj (the Python binding of PROJ) if installed."""

    def __init__(self, epsg):
        from pyproj import Transformer, CRS
        crs = CRS.from_epsg(int(epsg))
        self.name, self.code = f"{crs.name} (EPSG:{epsg})", str(epsg)
        self._f = Transformer.from_crs(4326, crs, always_xy=True)
        self._i = Transformer.from_crs(crs, 4326, always_xy=True)

    def forward(self, lat, lon):
        return self._f.transform(lon, lat)

    def inverse(self, x, y):
        lon, lat = self._i.transform(x, y)
        return lat, lon


def make_projection(spec, lat=0.0, lon=0.0):
    """spec: '3857' (default), 'utm', or an EPSG code like '32634' / 'EPSG:2100'."""
    s = str(spec or "3857").strip().upper().replace("EPSG:", "")
    if s in ("3857", "900913", "WEBMERC", "MERCATOR"):
        return WebMercator()
    if s in ("UTM", "AUTO"):
        return TransverseMercator.utm_for(lat, lon)
    if s.isdigit():
        v = int(s)
        if 32601 <= v <= 32660 or 32701 <= v <= 32760:
            zone, south = v % 100, v >= 32700
            return TransverseMercator(zone * 6 - 183, fn=10000000.0 if south else 0.0,
                                      name=f"UTM zone {zone}{'S' if south else 'N'} (EPSG:{v})",
                                      code=str(v))
        try:
            return PyprojProjection(v)
        except ImportError:
            raise ValueError(f"EPSG:{v} needs the pyproj package (pip install pyproj). "
                             "Built in: 3857 (Web Mercator) and UTM.")
        except Exception as e:  # noqa: BLE001 - pyproj errors vary by version
            raise ValueError(f"Unknown or unsupported EPSG:{v} ({e})")
    raise ValueError(f"Projection '{spec}': use 3857, utm, or an EPSG number")


MODELS = {"axis": "Per-axis, no rotation (as GameStatExporter)",
          "similarity": "Uniform scale + rotation"}


class Georef:
    """Game map (x east, y south) -> projected metres -> WGS84 lat/lon."""

    def __init__(self, proj, model, params, points):
        self.proj, self.model, self.params, self.points = proj, model, params, points
        self.residuals = [haversine(*self.to_latlon(*p["xy"]), *p["ll"]) for p in points]

    @classmethod
    def fit(cls, points, projection="3857", model="axis"):
        """points: list of dict(xy=(x, y), ll=(lat, lon), label=str); 2 or more."""
        if len(points) < 2:
            raise ValueError("At least two reference points are needed.")
        proj = make_projection(projection, *points[0]["ll"])
        P = [proj.forward(*p["ll"]) for p in points]
        xs = [p["xy"][0] for p in points]
        ys = [p["xy"][1] for p in points]
        if model == "axis":
            def lsq(u, v):
                mu, mv = sum(u) / len(u), sum(v) / len(v)
                suu = sum((a - mu) ** 2 for a in u)
                if suu < 1e-9:
                    return None
                k = sum((a - mu) * (b - mv) for a, b in zip(u, v)) / suu
                return k, mv - k * mu
            fx = lsq(xs, [q[0] for q in P])
            fy = lsq(ys, [q[1] for q in P])
            spread_x = max(xs) - min(xs)
            spread_y = max(ys) - min(ys)
            if not fx or not fy or spread_x < 500 or spread_y < 500:
                raise ValueError(
                    "With the per-axis model the reference points must be well apart both "
                    f"east-west and north-south on the game map (now {spread_x:.0f} × "
                    f"{spread_y:.0f} units apart). Diagonally opposite corners work best, "
                    "or switch to the uniform scale + rotation model.")
            params = (fx, fy)
        elif model == "similarity":
            z = [complex(x, -y) for x, y in zip(xs, ys)]
            w = [complex(*q) for q in P]
            mz, mw = sum(z) / len(z), sum(w) / len(w)
            szz = sum(abs(a - mz) ** 2 for a in z)
            if szz < 1e-6:
                raise ValueError("The reference points are at the same map position.")
            a = sum((b - mw) * (c - mz).conjugate() for b, c in zip(w, z)) / szz
            params = (a, mw - a * mz)
        else:
            raise ValueError(f"Unknown model {model!r}")
        return cls(proj, model, params, points)

    def to_projected(self, x, y):
        if self.model == "axis":
            (kx, bx), (ky, by) = self.params
            return kx * x + bx, ky * y + by
        a, b = self.params
        w = a * complex(x, -y) + b
        return w.real, w.imag

    def to_latlon(self, x, y):
        return self.proj.inverse(*self.to_projected(x, y))

    # ---- diagnostics -------------------------------------------------------
    def ground_scale(self):
        """Real metres per game unit along the map's x and y axes, and how far
        the map's 'up' is turned from true north (degrees, + = clockwise)."""
        cx = sum(p["xy"][0] for p in self.points) / len(self.points)
        cy = sum(p["xy"][1] for p in self.points) / len(self.points)
        d = 1000.0
        c = self.to_latlon(cx, cy)
        ex = self.to_latlon(cx + d, cy)
        ny = self.to_latlon(cx, cy - d)
        sx = haversine(*c, *ex) / d
        sy = haversine(*c, *ny) / d
        dlat = ny[0] - c[0]
        dlon = (ny[1] - c[1]) * math.cos(math.radians(c[0]))
        rot = math.degrees(math.atan2(dlon, dlat))
        return sx, sy, rot

    def pair_distances(self):
        """(map distance, real distance) between the first two points."""
        p, q = self.points[0], self.points[1]
        return math.dist(p["xy"], q["xy"]), haversine(*p["ll"], *q["ll"])

    def report(self):
        """Returns (text, problems). problems is a list of serious issues."""
        sx, sy, rot = self.ground_scale()
        lines = [f"Projection: {self.proj.name}", f"Model: {MODELS[self.model]}",
                 f"Ground scale: {sx:.3f} m per game unit east-west, {sy:.3f} north-south"
                 + (f"; map 'up' is {rot:+.1f}° from true north" if self.model == "similarity" else "")]
        problems, notes = [], []
        dm, dr = self.pair_distances()
        if dm > 0:
            lines.append(f"Points 1–2: {dm / 1000:.2f} km apart on the game map, "
                         f"{dr / 1000:.2f} km apart in the real world")
        for s, axis in ((sx, "east-west"), (sy, "north-south")):
            if not 0.5 <= s <= 2.0:
                problems.append(
                    f"The fit implies {s:.2f} real metres per game unit {axis}; Command Ops maps "
                    "are about 1. A reference coordinate is probably wrong (a typo, lat/lon "
                    "swapped, or a different place with the same name), or the game position "
                    "doesn't match the real place (map-edge exits such as 'To Larissa' are not the town).")
                break
        xs = [p["xy"][0] for p in self.points]
        ys = [p["xy"][1] for p in self.points]
        spx, spy = max(xs) - min(xs), max(ys) - min(ys)
        if self.model == "axis" and min(spx, spy) < 0.25 * max(spx, spy):
            axis_name = "east-west" if spx < spy else "north-south"
            notes.append(f"The points are nearly in a line ({axis_name} spread is only "
                         f"{100 * min(spx, spy) / max(spx, spy):.0f}% of the other), so the {axis_name} "
                         "scale is poorly determined. Use points far apart diagonally (map corners work "
                         "well), add a third point, or use the uniform scale + rotation model.")
        if self.model == "axis" and min(sx, sy) > 0 and max(sx, sy) / min(sx, sy) > 1.15:
            notes.append(f"East-west and north-south scales differ by "
                         f"{(max(sx, sy) / min(sx, sy) - 1) * 100:.0f}%; check the points.")
        if self.model == "similarity" and abs(rot) > 10:
            notes.append(f"The game map is turned {rot:+.0f}° from true north (some Command Ops "
                         "maps are; the per-axis model can't handle that, this one does).")
        if len(self.points) > 2:
            for p, r in zip(self.points, self.residuals):
                lines.append(f"  {p.get('label', '')[:40]}: off by {r:.0f} m")
            worst = max(self.residuals)
            if worst > 1000:
                problems.append(f"A reference point is {worst / 1000:.1f} km away from where the "
                                "fit puts it; one of the points is wrong.")
            elif worst > 250:
                notes.append(f"Largest point error is {worst:.0f} m.")
        text = "\n".join(lines + [f"Note: {n}" for n in notes] + [f"PROBLEM: {p}" for p in problems])
        return text, problems


def invalid_positions(cog, georef, include_offmap=False):
    """Units/objectives whose lat/lon would be unusable (map.army rejects them)."""
    bad = []
    items = [(u["name"], u["x"], u["y"]) for u in cog.units if include_offmap or not u["offmap"]]
    items += [(o["name"], o["x"], o["y"]) for o in cog.objectives]
    for name, x, y in items:
        try:
            lat, lon = georef.to_latlon(x, y)
        except (ValueError, OverflowError):
            bad.append(name)
            continue
        if not (math.isfinite(lat) and math.isfinite(lon)) or abs(lat) > 85.0 or abs(lon) > 180:
            bad.append(name)
    return bad


def parse_game_xy(text):
    """'12345, 6789' -> (12345.0, 6789.0), else None."""
    m = re.fullmatch(r"\s*\(?\s*(-?\d+(?:\.\d+)?)\s*[,;\s]\s*(-?\d+(?:\.\d+)?)\s*\)?\s*", text or "")
    return (float(m.group(1)), float(m.group(2))) if m else None


def parse_latlon(text):
    """Accepts '39.89, 22.19', '39.89 22.19', or with N/S/E/W suffixes."""
    t = text.strip().upper().replace(";", ",")
    parts = [p for p in re.split(r"[,\s]+", t) if p]
    if len(parts) != 2:
        raise ValueError(f"Can't read '{text}': enter it as 'lat, lon', for example 39.89, 22.19")
    vals = []
    for p in parts:
        sign = -1 if p.endswith(("S", "W")) or p.startswith("-") else 1
        num = float(p.strip("NSEW+-°"))
        vals.append(sign * num)
    lat, lon = vals
    if not (-90 <= lat <= 90 and -180 <= lon <= 180):
        raise ValueError(f"Coordinates out of range: {text}")
    return lat, lon


# --------------------------------------------------------------------------
# MilX (.milxly) output for map.army
# --------------------------------------------------------------------------

MILX_NS = "http://gs-soft.com/MilX/V3.1"
XSI_NS = "http://www.w3.org/2001/XMLSchema-instance"
MSS_LIBRARY_VERSION = "2025.02.20"
LABEL_MAX = 21          # map.army labels get cramped beyond about 21 characters

# Words that end a unit's own designation; the rest of the name is its parent.
_SPLIT_WORDS = ("Coy", "Bty", "Sqn", "Pl", "Tp", "HQ", "Column")


def _clean(text):
    return re.sub(r"[\"'<>&]", "", text).strip()


def _shorten_ex(text):
    """Compress a long label. Returns (label, was_hard_truncated)."""
    t = _clean(text)
    if len(t) <= LABEL_MAX:
        return t, False
    t = re.sub(r"\s+", " ", re.sub(r"\(.*?\)", "", t)).strip()
    steps = [(r"\b(\d+)(st|nd|rd|th)\b", r"\1"), (r",", ""), (r"\bRailway\b", "Rly"),
             (r"\bTunnel\b", "Tnl"), (r"\bBridge\b", "Br"), (r"\bNorth\b", "N"),
             (r"\bSouth\b", "S"), (r"\bSchuetzen\b", "Schtz"), (r"\bRegt\b", "R"),
             (r"\bBty\b", "Bt"), (r"\bMot\b", "M"), (r"\bCoy\b", "C"), (r"\bInf\b", "I")]
    for pat, rep in steps:
        t = re.sub(pat, rep, t).strip()
        if len(t) <= LABEL_MAX:
            return t, False
    return t[:LABEL_MAX].rstrip(), True


def _shorten(text):
    return _shorten_ex(text)[0]


def unit_labels(unit):
    """Return (T, M): the unit's own designation and its parent formation."""
    words = _clean(unit["name"]).split()
    cut = None
    for i, w in enumerate(words):
        w = w.rstrip(",")
        nxt = words[i + 1] if i + 1 < len(words) else ""
        if w in _SPLIT_WORDS or (w == "Bn" and nxt and nxt != "HQ" and not nxt[0].isdigit()):
            cut = i + 1
            if w == "Column" and len(nxt) <= 2:
                cut = i + 2          # Mot Bridge Column B | Pnr Bn 38
            break
    if cut is None or cut >= len(words):
        own, parent = " ".join(words), ""
    else:
        own, parent = " ".join(words[:cut]).rstrip(","), " ".join(words[cut:])
    t, cut_off = _shorten_ex(own)
    if cut_off and unit.get("short"):     # still too long: use the game's own short code
        t = _shorten(unit["short"])
    return t, _shorten(parent)


def objective_symbol(held_by_friendly, held_by_enemy):
    # "Check Point" point graphic (GFGPGPPK). Affiliation: who holds it now.
    aff = "H" if held_by_enemy and not held_by_friendly else "F"
    return f"G{aff}GPGPPK-------"


def milx_layer(layer_name, graphics):
    """graphics: list of dicts with sidc, optional M/T/W/H/J text fields, and either
    lat/lon (one point) or pts [(lat, lon), ...]. Returns XML text."""
    def esc(t):
        return html.escape(t, quote=True)

    out = ['<?xml version="1.0" encoding="UTF-8" standalone="no"?>',
           f'<MilXDocument_Layer xmlns="{MILX_NS}" xmlns:xsi="{XSI_NS}">',
           f"  <MssLibraryVersionTag>{MSS_LIBRARY_VERSION}</MssLibraryVersionTag>",
           "  <MilXLayer>",
           f"    <Name>{esc(layer_name)}</Name>",
           "    <LayerType>Normal</LayerType>",
           "    <GraphicList>"]
    for g in graphics:
        inner = f'<Symbol ID="{g["sidc"]}">'
        for key in ("M", "T", "W", "H", "J"):      # 2525 modifier fields
            if g.get(key):
                inner += f'<Attribute ID="{key}">{esc(g[key])}</Attribute>'
        inner += "</Symbol>"
        pts = g.get("pts") or [(g["lat"], g["lon"])]
        out += ["      <MilXGraphic>",
                f"        <MssStringXML>{esc(inner)}</MssStringXML>",
                "        <PointList>"]
        for lat, lon in pts:
            out += ["          <Point>",
                    f"            <X>{lon:.8f}</X>",
                    f"            <Y>{lat:.8f}</Y>",
                    "          </Point>"]
        out += ["        </PointList>",
                "        <SysCustPropList>",
                '          <CustProp SystemID="gs-soft_ma" Name="SDZ" DataType="dt_string" Value=""/>',
                "        </SysCustPropList>",
                "      </MilXGraphic>"]
    out += ["    </GraphicList>",
            "    <CoordSystemType>WGS84</CoordSystemType>",
            "    <ViewScale>0.1</ViewScale>",
            "    <SymbolSize>1</SymbolSize>",
            "  </MilXLayer>",
            "</MilXDocument_Layer>", ""]
    return "\n".join(out)


POSTURES = ["Undeployed", "Taking Cover", "Deployed", "Dug In", "Entrenched", "Fortified"]
ENEMY_MODES = {"fog": "FOG OF WAR", "all": "ALL (GOD'S EYE)", "none": "HIDDEN"}


def _enemy_mode(v):
    if v is True:
        return "fog"
    if v is False or v is None:
        return "none"
    return v if v in ENEMY_MODES else "fog"


def estimated_label(estab_entry):
    """'1m-nz.id-Inf Coy (-)' -> 'Inf Coy (-)'."""
    n = (estab_entry or {}).get("name", "") or "Unidentified"
    parts = n.split("-", 2)
    return _shorten(parts[2] if len(parts) == 3 and len(parts[0]) <= 3 else n)


def shown_units(cog, friendly_side, enemy_mode="fog", include_offmap=False, rules=None):
    """The units to draw/export: friendly units as they are; enemy units either as
    your side knows them ('fog'), as they really are ('all'), or not at all ('none').
    Returns dicts: x, y, side, sidc, T, M, stale, friendly."""
    mode = _enemy_mode(enemy_mode)
    out = []
    intel = cog.intel.get(friendly_side, {})
    for u in cog.units:
        if u["side"] is None:
            continue
        mine = u["side"] == friendly_side
        if not mine and mode == "none":
            continue
        if mine or mode == "all":
            if u["offmap"] and not include_offmap:
                continue
            t, m = unit_labels(u)
            out.append(dict(x=u["x"], y=u["y"], side=u["side"], sidc=sidc_for(u, friendly_side, rules),
                            T=t, M=m, stale=False, friendly=mine))
            continue
        rec = intel.get(u["uid"])
        if not rec or rec["status"] == "unknown":
            continue
        guess = dict(side=u["side"], name=(rec["estab"] or {}).get("name", ""), estab=rec["estab"])
        sidc = sidc_for(guess, friendly_side, rules)
        stale = rec["status"] == "last_seen"
        if stale:
            sidc = sidc[:3] + "A" + sidc[4:]          # 2525: 'anticipated' = dashed frame
        when = rec["last_seen"].strftime("%H:%M") if rec["last_seen"] else ""
        rep_t = rec["last_seen"] if stale else rec["reported"]
        conf = rec["confidence"]
        if stale and not conf:
            conf = None                                    # no current confidence for a lost contact
        source = likely_source(cog, friendly_side, rec["x"], rec["y"])
        info = []
        if conf is not None:
            info.append(f"conf {conf}%")
        if rec["posture"]:
            info.append(rec["posture"])
        if source:
            info.append(f"by {source}?")
        out.append(dict(x=rec["x"], y=rec["y"], side=u["side"], sidc=sidc,
                        T=estimated_label(rec["estab"]),
                        M=(f"last seen {when}" if stale else ""), stale=stale, friendly=False,
                        W=dtg(rep_t), H=" · ".join(info), J=evaluation_rating(conf, source),
                        seen=rep_t.strftime("%H:%M") if rep_t else "", conf=conf, source=source))
    return out


def dtg(t):
    """2525 date-time group, e.g. 191217ZAPR41 (game time, no zone)."""
    return t.strftime("%d%H%MZ%b%y").upper() if t else ""


def evaluation_rating(conf, source):
    """2525 field J: source reliability (A-F) + information credibility (1-6)."""
    if conf is None:
        return ("B" if source else "F") + "6"            # 6 = truth cannot be judged
    cred = 1 if conf >= 90 else 2 if conf >= 70 else 3 if conf >= 50 else 4 if conf >= 30 else 5
    return ("B" if source else "F") + str(cred)


def likely_source(cog, friendly_side, x, y, max_range=3000):
    """The save doesn't say who reported a contact; name the nearest own unit
    within max_range metres as the probable source (or '' if none)."""
    best = None
    for u in cog.units:
        if u["side"] != friendly_side or u["offmap"]:
            continue
        d = math.hypot(u["x"] - x, u["y"] - y)
        if d <= max_range and (best is None or d < best[0]):
            best = (d, u)
    return unit_labels(best[1])[0] if best else ""


# --------------------------------------------------------------------------
# Orders as tactical graphics
# --------------------------------------------------------------------------

# Arrow graphics: MIL-STD-2525C puts the arrowhead at the first point. If map.army
# draws them backwards, set this to False.
ARROW_TIP_FIRST = True

ORDER_GRAPHIC = {   # task type -> (kind, 2525C category + function)
    "Move": ("arrow", "G", "OLKGS-"), "Exit": ("arrow", "G", "OLKGS-"),
    "Probe": ("arrow", "G", "OLKGS-"), "Construct Bridge": ("arrow", "G", "OLKGS-"),
    "Attack": ("arrow", "G", "OLKGM-"), "Assault": ("arrow", "G", "OLKGM-"),
    "Destroy": ("arrow", "G", "OLKGM-"), "Cross River Assault": ("arrow", "G", "OLKGM-"),
    "Secure": ("arrow", "G", "OLKGM-"), "Secure Crossing": ("arrow", "G", "OLKGM-"),
    "Withdraw": ("arrow", "T", "W-----"), "Delay": ("arrow", "T", "L-----"),
    "Defend": ("area", "G", "DAB---"), "Hold": ("area", "G", "DAB---"),
    "Deny Crossing": ("area", "G", "DAB---"),
    "Rest": ("area", "G", "GAA---"), "Reorg": ("area", "G", "GAA---"),
    "Bombard": ("target", "F", "PTS---"), "On Call Support": ("target", "F", "PTS---"),
    "Fire": ("target", "F", "PTS---"),
}


def graphic_sidc(aff, cat, func):
    return f"G{aff}{cat}P{func}----X"


def order_items(cog, friendly_side, include_enemy=False):
    """Current orders as drawable items: dict(kind, type, sidc, pts (game x,y), T, W, H, friendly)."""
    items = []
    for u in cog.units:
        o = u.get("order")
        if not o or u["offmap"] or u["side"] is None:
            continue
        mine = u["side"] == friendly_side
        if not mine and not include_enemy:
            continue
        g = ORDER_GRAPHIC.get(o["label"])
        if not g:
            continue
        kind, cat, func = g
        tx, ty = (o["x"], o["y"]) if o["x"] >= 0 and o["y"] >= 0 else (u["x"], u["y"])
        if kind == "arrow" and math.hypot(tx - u["x"], ty - u["y"]) < 150:
            continue                                    # already there: nothing to draw
        if kind == "arrow":
            pts = [(tx, ty), (u["x"], u["y"])] if ARROW_TIP_FIRST else [(u["x"], u["y"]), (tx, ty)]
        elif kind == "area":
            r = 300 if u.get("estab") is None or u["estab"].get("size") not in ("battalion", "brigade") else 600
            pts = [(tx + r * math.cos(k * math.pi / 4), ty + r * math.sin(k * math.pi / 4)) for k in range(8)]
        else:
            pts = [(tx, ty)]
        due = o.get("due")
        info = o["label"] + (f", due {due.strftime('%d %H:%M')}" if due and due.year < 1990 and due > cog.clock else "")
        items.append(dict(kind=kind, type=o["label"], sidc=graphic_sidc("F" if mine else "H", cat, func),
                          pts=pts, T=unit_labels(u)[0], W=dtg(due) if due and due > cog.clock else "",
                          H=info, friendly=mine))
    return items


def build_layers(cog, georef, friendly_side, want_friendly=True, want_enemy="fog",
                 want_objectives=True, include_ai=False, include_offmap=False, rules=None,
                 want_orders=True):
    """Returns a list of (suffix, layer_name, xml_text, count).
    want_enemy: 'fog' (what your side knows), 'all' (true positions) or 'none'."""
    stamp = cog.clock.strftime("%d %b %H%M")
    layers = []
    mode = _enemy_mode(want_enemy)
    units = shown_units(cog, friendly_side, mode, include_offmap, rules)

    def graphics(pred):
        gs = []
        for su in units:
            if pred(su):
                lat, lon = georef.to_latlon(su["x"], su["y"])
                gs.append(dict(sidc=su["sidc"], T=su["T"], M=su["M"], W=su.get("W", ""),
                               H=su.get("H", ""), J=su.get("J", ""), lat=lat, lon=lon))
        return gs

    if want_friendly:
        gs = graphics(lambda su: su["friendly"])
        name = f"Friendly {stamp}"
        layers.append(("Friendly", name, milx_layer(name, gs), len(gs)))
    if mode != "none":
        gs = graphics(lambda su: not su["friendly"])
        name = f"Enemy {'intel' if mode == 'fog' else 'actual'} {stamp}"
        layers.append(("Enemy", name, milx_layer(name, gs), len(gs)))
    if want_objectives:
        by_name = collections.OrderedDict()
        for ob in cog.objectives:
            if ob["ai"] and not include_ai:
                continue
            by_name.setdefault(ob["name"], []).append(ob)
        gs = []
        for nm, obs in by_name.items():
            x = sum(o["x"] for o in obs) / len(obs)
            y = sum(o["y"] for o in obs) / len(obs)
            lat, lon = georef.to_latlon(x, y)
            fr = any(o["held"] and o["side"] == friendly_side for o in obs)
            en = any(o["held"] and o["side"] != friendly_side for o in obs)
            status = "held" if fr else ("enemy held" if en else "")
            gs.append(dict(sidc=objective_symbol(fr, en), T=_shorten(nm), M=status,
                           lat=lat, lon=lon))
        name = f"Objectives {stamp}"
        layers.append(("Objectives", name, milx_layer(name, gs), len(gs)))
    if want_orders:
        gs = []
        for it in order_items(cog, friendly_side, include_enemy=(mode == "all")):
            gs.append(dict(sidc=it["sidc"], T=it["T"], W=it["W"], H=it["H"],
                           pts=[georef.to_latlon(x, y) for x, y in it["pts"]]))
        name = f"Orders {stamp}"
        layers.append(("Orders", name, milx_layer(name, gs), len(gs)))
    return layers


def write_layers(layers, out_base):
    """out_base: path without extension. Returns written paths."""
    paths = []
    for suffix, _name, xml, _n in layers:
        p = f"{out_base}.{suffix}.milxly"
        with open(p, "w", encoding="utf-8") as f:
            f.write(xml)
        paths.append(p)
    return paths


# --------------------------------------------------------------------------
# Remembered georeferences (per scenario title)
# --------------------------------------------------------------------------

PREFS = os.path.join(os.path.expanduser("~"), ".cog2milxly.json")


def load_prefs():
    try:
        with open(PREFS, "r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def save_prefs(p):
    try:
        with open(PREFS, "w", encoding="utf-8") as f:
            json.dump(p, f, indent=2)
    except OSError:
        pass


# --------------------------------------------------------------------------
# GUI: the scenario map with all units; click two points, then export
# --------------------------------------------------------------------------

def run_gui():
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox
    try:
        from PIL import Image, ImageTk
    except ImportError:
        root = tk.Tk()
        root.withdraw()
        messagebox.showerror("Pillow needed", "This tool draws the map with Pillow.\n\n"
                             "Install it once with:\n    pip install pillow")
        return

    root = tk.Tk()
    root.title("co2milxly v2")
    root.geometry("1200x860")
    prefs = load_prefs()
    S = dict(base=None, cog=None, mapf=None, ppm=0.1, terrain=None, scene=None, photo=None,
             refs=[], zoom=1.0, ox=0.0, oy=0.0, drag=None, georef=None)

    # ---- top bar ----------------------------------------------------------
    bar = ttk.Frame(root, padding=(8, 6))
    bar.pack(fill="x")
    ttk.Button(bar, text="Open save…", command=lambda: open_save()).pack(side="left")
    ttk.Button(bar, text="Game folder…", command=lambda: choose_base(ask=True)).pack(side="left", padx=(6, 0))
    ttk.Label(bar, text="Enemy:").pack(side="left", padx=(14, 4))
    enemy_choice = tk.StringVar(value=ENEMY_MODES["fog"])
    enemy_cb = ttk.Combobox(bar, textvariable=enemy_choice, values=list(ENEMY_MODES.values()),
                            state="readonly", width=24)
    enemy_cb.pack(side="left")

    def enemy_mode():
        return next((k for k, v in ENEMY_MODES.items() if v == enemy_choice.get()), "fog")
    enemy_cb.bind("<<ComboboxSelected>>", lambda e: (compose(), redraw(), enemy_cb.selection_clear()))
    orders_var = tk.BooleanVar(value=True)
    ttk.Checkbutton(bar, text="Orders", variable=orders_var,
                    command=lambda: (compose(), redraw())).pack(side="left", padx=(12, 0))
    clear_btn = ttk.Button(bar, text="Clear points", command=lambda: clear_points())
    exp_milx = ttk.Button(bar, text="EXPORT MILXLY", command=lambda: export_milx())
    exp_img = ttk.Button(bar, text="EXPORT IMAGE", command=lambda: export_image())
    info_var = tk.StringVar(value="")
    ttk.Label(root, textvariable=info_var, padding=(10, 0), foreground="#444").pack(fill="x")
    fit_var = tk.StringVar(value="")
    fit_lbl = ttk.Label(root, textvariable=fit_var, padding=(10, 0, 10, 4))
    fit_lbl.pack(fill="x")
    canvas = tk.Canvas(root, background="#2b2b2b", highlightthickness=0, cursor="crosshair")
    canvas.pack(fill="both", expand=True)

    def update_buttons():
        for b in (exp_img, exp_milx, clear_btn):
            b.pack_forget()
        if len(S["refs"]) >= 2 and S["georef"] is not None:
            exp_milx.pack(side="right")
            exp_img.pack(side="right", padx=(0, 6))
        if S["refs"]:
            clear_btn.pack(side="right", padx=(0, 12))

    # ---- game folder ------------------------------------------------------
    def choose_base(ask=False, hints=()):
        base = None if ask else prefs.get("_base")
        if base and not os.path.isdir(base):
            base = None
        if not base and not ask:
            base = find_game_install(list(hints) + [prefs.get("_recent")])
        if not base:
            if not ask:
                messagebox.showinfo("Command Ops 2 folder",
                                    "Couldn't find where Command Ops 2 is installed.\n\n"
                                    "Please pick the folder that contains CmdOps.exe.")
            base = filedialog.askdirectory(title="Folder containing CmdOps.exe")
            if not base:
                return S["base"]
            if not _has_exe(base) and not os.path.isdir(os.path.join(base, "Maps")):
                if not messagebox.askyesno("Command Ops 2 folder",
                                           "There's no CmdOps.exe in that folder. Use it anyway?"):
                    return S["base"]
        S["base"] = base
        prefs["_base"] = base
        save_prefs(prefs)
        if not S["cog"]:
            info_var.set(f"Game folder: {base}.  Open a save to begin.")
        return base

    # ---- loading ----------------------------------------------------------
    def open_save(path=None):
        if not path:
            init = S["base"]
            if init:
                for sd in ("Saved Games", "SavedGames", "Saves"):
                    if os.path.isdir(os.path.join(init, sd)):
                        init = os.path.join(init, sd)
                        break
            path = filedialog.askopenfilename(title="Open Command Ops 2 save", initialdir=init or None,
                                              filetypes=[("Command Ops saves", "*.cog"), ("All files", "*.*")])
            if not path:
                return
        try:
            cog = CogFile(path)
        except Exception as e:  # noqa: BLE001
            messagebox.showerror("Could not read file", f"{path}\n\n{e}")
            return
        base = S["base"] or find_game_install([path])
        if base and not S["base"]:
            S["base"] = base
            prefs["_base"] = base
        est = (find_in_install(base, cog.estab_name, ("Estabs", "Estab", "Data")) if base else None) \
            or find_estab(cog)
        if est:
            try:
                cog.attach_estab(Estab(est))
            except Exception:  # noqa: BLE001
                est = None
        mp = (find_in_install(base, cog.map_name, ("Maps", "maps")) if base else None) \
            or find_game_file(cog, cog.map_name)
        mapf = None
        if mp:
            try:
                mapf = MapFile(mp)
            except Exception:  # noqa: BLE001
                mapf = None
        S.update(cog=cog, mapf=mapf, refs=[], georef=None)
        if mapf and mapf.width:
            wm, hm = mapf.width, mapf.height
        else:
            xs = [u["x"] for u in cog.units if not u["offmap"]] + [o["x"] for o in cog.objectives]
            ys = [u["y"] for u in cog.units if not u["offmap"]] + [o["y"] for o in cog.objectives]
            wm, hm = max(xs + [1000]) + 1000, max(ys + [1000]) + 1000
        S["ppm"] = min(0.1, 4000.0 / max(wm, hm))
        root.config(cursor="watch")
        info_var.set("Drawing the map…")
        root.update()
        S["terrain"] = render_terrain(mapf, wm, hm, S["ppm"])
        root.config(cursor="")
        compose()
        fit_view()
        side = cog.forces.get(cog.human_side, "your side")
        notes = []
        if not mapf:
            notes.append(f"map {cog.map_name} not found in the game folder (plain grid shown)")
        if not est:
            notes.append("unit database not found (symbols guessed from names)")
        info_var.set(f"{cog.title} · {fmt_time(cog.clock)} · You: {side} · "
                     f"{sum(1 for u in cog.units if not u['offmap'])} units"
                     + (f"  —  {'; '.join(notes)}" if notes else ""))
        saved = prefs.get(cog.title, {}).get("map_refs") or []
        for r in saved[:2]:
            try:
                S["refs"].append(dict(xy=tuple(r["xy"]), ll=tuple(r["ll"]), label=r.get("label", "")))
            except (KeyError, TypeError):
                pass
        refit()
        prefs["_recent"] = path
        save_prefs(prefs)

    def compose():
        if S["terrain"] is None:
            return
        S["scene"] = render_scene(S["terrain"], S["ppm"], S["cog"], S["cog"].human_side, enemy_mode(),
                                  show_orders=orders_var.get())

    # ---- view: zoom / pan --------------------------------------------------
    def fit_view():
        if S["scene"] is None:
            return
        cw, ch = max(canvas.winfo_width(), 100), max(canvas.winfo_height(), 100)
        z = min(cw / S["scene"].width, ch / S["scene"].height)
        S["zoom"] = z
        S["ox"] = -(cw / z - S["scene"].width) / 2
        S["oy"] = -(ch / z - S["scene"].height) / 2
        redraw()

    def redraw(fast=False):
        canvas.delete("all")
        sc = S["scene"]
        if sc is None:
            canvas.create_text(canvas.winfo_width() / 2, canvas.winfo_height() / 2, fill="#ddd",
                               text="Open a Command Ops 2 save to see its map.", font=("TkDefaultFont", 13))
            return
        cw, ch = max(canvas.winfo_width(), 1), max(canvas.winfo_height(), 1)
        z, ox, oy = S["zoom"], S["ox"], S["oy"]
        x0, y0 = max(0, ox), max(0, oy)
        x1, y1 = min(sc.width, ox + cw / z), min(sc.height, oy + ch / z)
        if x1 > x0 and y1 > y0:
            crop = sc.crop((int(x0), int(y0), int(math.ceil(x1)), int(math.ceil(y1))))
            w, h = max(1, int(crop.width * z)), max(1, int(crop.height * z))
            img = crop.resize((w, h), Image.NEAREST if fast else Image.BILINEAR)
            S["photo"] = ImageTk.PhotoImage(img)
            canvas.create_image((int(x0) - ox) * z, (int(y0) - oy) * z, anchor="nw", image=S["photo"])
        for i, r in enumerate(S["refs"]):
            cx, cy = to_canvas(*r["xy"])
            canvas.create_oval(cx - 11, cy - 11, cx + 11, cy + 11, outline="#d000a0", width=3)
            canvas.create_line(cx - 18, cy, cx + 18, cy, fill="#d000a0", width=2)
            canvas.create_line(cx, cy - 18, cx, cy + 18, fill="#d000a0", width=2)
            canvas.create_text(cx + 16, cy - 16, anchor="sw", fill="#d000a0", font=("TkDefaultFont", 11, "bold"),
                               text=f"{i + 1}: {r['ll'][0]:.4f}, {r['ll'][1]:.4f}")
        if len(S["refs"]) < 2:
            canvas.create_text(12, 12, anchor="nw", fill="#ffffff", font=("TkDefaultFont", 11, "bold"),
                               text=f"Click a place you can find on a real map to set reference point "
                                    f"{len(S['refs']) + 1} of 2.   Scroll to zoom, drag to move.")

    def to_canvas(gx, gy):
        p = S["ppm"]
        return (gx * p - S["ox"]) * S["zoom"], (gy * p - S["oy"]) * S["zoom"]

    def to_game(cx, cy):
        p = S["ppm"]
        return (cx / S["zoom"] + S["ox"]) / p, (cy / S["zoom"] + S["oy"]) / p

    def on_wheel(e):
        if S["scene"] is None:
            return
        f = 1.25 if (getattr(e, "delta", 0) > 0 or getattr(e, "num", 0) == 4) else 0.8
        sx, sy = e.x / S["zoom"] + S["ox"], e.y / S["zoom"] + S["oy"]
        S["zoom"] = max(0.05, min(8.0, S["zoom"] * f))
        S["ox"], S["oy"] = sx - e.x / S["zoom"], sy - e.y / S["zoom"]
        redraw()

    def on_press(e):
        S["drag"] = (e.x, e.y, S["ox"], S["oy"], False)

    def on_motion(e):
        if not S["drag"]:
            return
        x, y, ox, oy, moved = S["drag"]
        if moved or abs(e.x - x) + abs(e.y - y) > 4:
            S["drag"] = (x, y, ox, oy, True)
            S["ox"], S["oy"] = ox - (e.x - x) / S["zoom"], oy - (e.y - y) / S["zoom"]
            redraw(fast=True)

    def on_release(e):
        d = S["drag"]
        S["drag"] = None
        if d and d[4]:
            redraw()
            return
        if S["scene"] is None:
            return
        if len(S["refs"]) >= 2:
            messagebox.showinfo("Reference points", "Both points are set. Use 'Clear points' to start again.")
            return
        add_point(*to_game(e.x, e.y))

    canvas.bind("<ButtonPress-1>", on_press)
    canvas.bind("<B1-Motion>", on_motion)
    canvas.bind("<ButtonRelease-1>", on_release)
    canvas.bind("<MouseWheel>", on_wheel)
    canvas.bind("<Button-4>", on_wheel)
    canvas.bind("<Button-5>", on_wheel)
    canvas.bind("<Configure>", lambda e: redraw() if S["scene"] is not None else redraw())

    # ---- reference points ----------------------------------------------------
    def nearest_place(gx, gy):
        best = None
        cand = dict(S["mapf"].places) if S["mapf"] else {}
        for o in S["cog"].objectives:
            if not o["ai"]:
                cand.setdefault(o["name"], (o["x"], o["y"]))
        for nm, (x, y) in cand.items():
            dd = math.hypot(x - gx, y - gy)
            if best is None or dd < best[1]:
                best = (nm, dd)
        return best

    def ask_latlon(gx, gy):
        dlg = tk.Toplevel(root)
        dlg.title(f"Reference point {len(S['refs']) + 1}")
        dlg.transient(root)
        dlg.resizable(False, False)
        near = nearest_place(gx, gy)
        msg = f"Game position {gx:.0f}, {gy:.0f}"
        if near and near[1] < 3000:
            msg += f"  —  {near[1]:.0f} m from '{near[0]}'"
        ttk.Label(dlg, text=msg, padding=(12, 12, 12, 4)).pack(anchor="w")
        ttk.Label(dlg, text="Its real latitude, longitude (e.g. 39.8817, 22.2283):",
                  padding=(12, 0)).pack(anchor="w")
        v = tk.StringVar()
        ent = ttk.Entry(dlg, textvariable=v, width=34)
        ent.pack(padx=12, pady=6, fill="x")
        err = ttk.Label(dlg, text="", foreground="#b00020", padding=(12, 0))
        err.pack(anchor="w")
        res = {}

        def ok(*_):
            try:
                res["ll"] = parse_latlon(v.get())
            except ValueError as ex:
                err.configure(text=str(ex))
                return
            dlg.destroy()
        btns = ttk.Frame(dlg, padding=12)
        btns.pack(fill="x")
        ttk.Button(btns, text="OK", command=ok).pack(side="right")
        ttk.Button(btns, text="Cancel", command=dlg.destroy).pack(side="right", padx=6)
        ent.bind("<Return>", ok)
        ent.focus_set()
        dlg.grab_set()
        root.wait_window(dlg)
        return res.get("ll"), (near[0] if near and near[1] < 3000 else "")

    def add_point(gx, gy):
        ll, label = ask_latlon(gx, gy)
        if not ll:
            return
        S["refs"].append(dict(xy=(gx, gy), ll=ll, label=label or f"{gx:.0f},{gy:.0f}"))
        refit()

    def clear_points():
        S["refs"] = []
        refit()

    def refit():
        S["georef"] = None
        fit_var.set("")
        fit_lbl.configure(foreground="#444")
        if len(S["refs"]) >= 2:
            try:
                g = Georef.fit(S["refs"], "3857", "similarity")
                _t, problems = g.report()
                sx, sy, rot = g.ground_scale()
                if problems or invalid_positions(S["cog"], g):
                    fit_var.set(f"These points don't fit: the map would be {max(sx, sy):.1f} m per game unit "
                                "(about 1 is right). Check the lat, lon values, then Clear points.")
                    fit_lbl.configure(foreground="#b00020")
                else:
                    fit_var.set(f"Georeferenced: {(sx + sy) / 2:.2f} m per game unit, map turned {rot:+.0f}° "
                                "from north.")
                    fit_lbl.configure(foreground="#1b7f3b")
                S["georef"] = g
            except ValueError as e:
                fit_var.set(str(e))
                fit_lbl.configure(foreground="#b00020")
        cog = S["cog"]
        if cog:
            prefs.setdefault(cog.title, {})["map_refs"] = [
                dict(xy=list(r["xy"]), ll=list(r["ll"]), label=r["label"]) for r in S["refs"]]
            save_prefs(prefs)
        update_buttons()
        redraw()

    # ---- exports ----------------------------------------------------------
    def export_image():
        cog = S["cog"]
        out = filedialog.asksaveasfilename(
            title="Export image", defaultextension=".png",
            initialfile=os.path.splitext(os.path.basename(cog.path))[0] + ".png",
            filetypes=[("PNG image", "*.png")])
        if not out:
            return
        root.config(cursor="watch")
        root.update()
        title = f"{cog.title}  ·  {fmt_time(cog.clock)}  ·  {cog.forces.get(cog.human_side, '')}"
        title += {"fog": "  ·  enemy: your intelligence", "all": "  ·  enemy: true positions",
                  "none": ""}[enemy_mode()]
        img = render_scene(S["terrain"], S["ppm"], cog, cog.human_side, enemy_mode(), S["refs"], title,
                           show_orders=orders_var.get())
        img.save(out)
        root.config(cursor="")
        messagebox.showinfo("Export image", f"Saved {os.path.basename(out)} ({img.width} × {img.height}).")

    def export_milx():
        cog, g = S["cog"], S["georef"]
        if invalid_positions(cog, g):
            messagebox.showerror("Export MILXLY", "With these points some units would land off the globe. "
                                 "Check the lat, lon values.")
            return
        _t, problems = g.report()
        if problems and not messagebox.askyesno("Export MILXLY", "The reference points don't fit well, so "
                                                "units will probably land in the wrong place. Export anyway?",
                                                icon="warning", default="no"):
            return
        out = filedialog.asksaveasfilename(
            title="Export MILXLY (one file per layer)", defaultextension=".milxly",
            initialfile=os.path.splitext(os.path.basename(cog.path))[0] + ".milxly",
            filetypes=[("MilX layer", "*.milxly")])
        if not out:
            return
        base = out[:-7] if out.lower().endswith(".milxly") else out
        layers = build_layers(cog, g, cog.human_side, True, enemy_mode(), True,
                              want_orders=orders_var.get())
        paths = write_layers(layers, base)
        messagebox.showinfo("Export MILXLY", "Saved:\n\n" + "\n".join(os.path.basename(p) for p in paths)
                            + "\n\nOpen each file in map.army as a layer.")

    # ---- start --------------------------------------------------------------
    def start():
        arg = sys.argv[1] if len(sys.argv) > 1 and sys.argv[1].lower().endswith(".cog") else None
        choose_base(hints=[arg] if arg else [])
        if arg:
            open_save(sys.argv[1])
        else:
            redraw()
    root.after(150, start)
    root.mainloop()


# --------------------------------------------------------------------------
# Command line (optional)
# --------------------------------------------------------------------------

def main():
    import argparse
    if len(sys.argv) <= 2 and not any(a.startswith("-") for a in sys.argv[1:]):
        run_gui()
        return
    ap = argparse.ArgumentParser(
        description="Convert a Command Ops 2 .cog save to map.army MilX layers (.milxly).")
    ap.add_argument("cog")
    ap.add_argument("out", nargs="?", help="output base name (default: next to the .cog)")
    ap.add_argument("--ref", nargs=2, action="append", metavar=("OBJECTIVE|X,Y", "LAT,LON"),
                    help="reference point: objective name or game 'x,y', and its real lat,lon "
                         "(give 2 to 4 times)")
    ap.add_argument("--proj", default="3857",
                    help="projection: 3857 (default, as GameStatExporter), utm, or an EPSG code")
    ap.add_argument("--model", choices=("axis", "similarity"), default="similarity",
                    help="similarity = scale + rotation (default; copes with rotated maps); "
                         "axis = per-axis, identical to GameStatExporter")
    ap.add_argument("--force", action="store_true", help="export even if the fit looks wrong")
    ap.add_argument("--no-friendly", action="store_true")
    ap.add_argument("--enemy", choices=("fog", "all", "none"), default="fog",
                    help="enemy units: fog = as your side knows them (default), all = true positions, none")
    ap.add_argument("--no-enemy", action="store_true", help="same as --enemy none")
    ap.add_argument("--no-objectives", action="store_true")
    ap.add_argument("--no-orders", action="store_true", help="skip the Orders layer")
    ap.add_argument("--ai", action="store_true", help="include AI waypoints")
    ap.add_argument("--offmap", action="store_true", help="include units not on the map")
    ap.add_argument("--friendly", type=int, help="side id to show as friendly (default: human side)")
    ap.add_argument("--estab", help="establishment file (.coe or .xml); default: search near the save")
    ap.add_argument("--rules", help="co2milxly-style co2milx.txt symbol rules (optional)")
    ap.add_argument("--list", action="store_true", help="list objectives and exit")
    a = ap.parse_args()
    cog = CogFile(a.cog)
    est_path = a.estab or find_estab(cog)
    if est_path:
        n = cog.attach_estab(Estab(est_path))
        print(f"establishment: {est_path} ({n}/{len(cog.units)} units matched)", file=sys.stderr)
    else:
        print(f"establishment {cog.estab_name} not found; guessing symbols from names "
              "(use --estab)", file=sys.stderr)
    rules = load_ruleset(a.rules) if a.rules else None
    if a.list:
        for o in cog.objectives:
            print(f"{o['side']}\t{o['name']}\t{o['x']}\t{o['y']}")
        return
    if not a.ref or len(a.ref) < 2:
        ap.error("give at least two --ref options")
    names = {}
    for o in cog.objectives:
        names.setdefault(o["name"], (o["x"], o["y"]))
    mp = find_game_file(cog, cog.map_name, [os.path.dirname(est_path)] if est_path else [])
    if mp:
        try:
            for nm, xy in MapFile(mp).places.items():
                names.setdefault(nm, xy)
        except Exception:  # noqa: BLE001
            pass
    pts = []
    for n, ll in a.ref:
        xy = names.get(n) or parse_game_xy(n)
        if xy is None:
            ap.error(f"no objective named {n!r} (use --list), and not a game 'x,y'")
        pts.append(dict(xy=xy, ll=parse_latlon(ll), label=n))
    try:
        g = Georef.fit(pts, a.proj, a.model)
    except ValueError as e:
        ap.error(str(e))
    text, problems = g.report()
    print(text, file=sys.stderr)
    bad = invalid_positions(cog, g, a.offmap)
    if bad:
        sys.exit(f"error: {len(bad)} positions fall outside valid lat/lon (e.g. {', '.join(bad[:3])}); "
                 "check the reference points")
    if problems and not a.force:
        sys.exit("error: the fit looks wrong (see PROBLEM above); fix the points or use --force")
    friendly = a.friendly or cog.human_side
    base = a.out or os.path.splitext(a.cog)[0]
    if base.lower().endswith(".milxly"):
        base = base[:-7]
    layers = build_layers(cog, g, friendly, not a.no_friendly, "none" if a.no_enemy else a.enemy,
                          not a.no_objectives, a.ai, a.offmap, rules, not a.no_orders)
    for p, (_s, _n, _x, n) in zip(write_layers(layers, base), layers):
        print(f"wrote {p} ({n} symbols)", file=sys.stderr)


if __name__ == "__main__":
    main()