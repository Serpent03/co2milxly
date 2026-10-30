"""
DATE
  26.04.25

DESCRIPTION
  This module covers the functionalities to convert
  a KML file generated from Command Ops 2's excellent
  GameStateExporter to a milxly XML file.
"""

import os
import sys
import subprocess
import traceback
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from xml.sax.saxutils import escape as xml_escape

from lxml import etree as ET

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


def generate_kml(game_dir: str, co2_savefile: str, xy1: list, xy2: list, ll1: list, ll2: list) -> list:
    gse = "GameStatExporter.exe"
    gse_path = os.path.join(game_dir, gse)

    if not os.path.exists(gse_path):
        raise FileNotFoundError(f"{gse} not found in directory: {game_dir}")

    kmls = []
    try:
        cmd = [
            gse_path,
            "--x1", str(xy1[0]),
            "--y1", str(xy1[1]),
            "--x2", str(xy2[0]),
            "--y2", str(xy2[1]),
            "--lat1", str(ll1[0]),
            "--lon1", str(ll1[1]),
            "--lat2", str(ll2[0]),
            "--lon2", str(ll2[1]),
            "--input", os.path.abspath(co2_savefile)
        ]

        result = subprocess.run(
            cmd,
            cwd=game_dir,
            check=True,
            capture_output=True,
            text=True
        )

        lines = result.stdout.split("\n")
        candidates = [line for line in lines if "Saved" in line]

        for candidate in candidates:
            actual = candidate.replace("Saved intel data to ", "").replace("Saved friendly data to ", "").strip()
            print(actual)
            if actual:
                full_kml_path = os.path.join(game_dir, actual)
                if os.path.exists(full_kml_path):
                    kmls.append(full_kml_path)

        return kmls
    except subprocess.CalledProcessError as e:
        print(f"Command failed with exit code {e.returncode}")
        print(f"Error output:\n{e.stderr}")
        print(f"Std output:\n{e.stdout}")
        print(f"Error args: {e.args}")
        raise e


def pretty_print(l):
    for k in l:
        print(f" --- {k['name']} --- ")
        print(f"Superior: {k['superior']:<20}")
        print(f"Type: {k['type']:<20}")
        print(f"Location: {str(k['location']):<20}\n")


def create_acronym(
    name: str, ignore_list: list, replace_list: list, special_words: list
) -> str:
    # Remove all odd characters including quotes that break XML/MilX
    for ch in [",", ".", '"', "'", "&", "<", ">"]:
        name = name.replace(ch, "")

    temp_list = list(filter(lambda x: x.lower() not in ignore_list, name.split()))

    p_start_idx = 0
    p_end_idx = -1
    for i, v in enumerate(temp_list):
        if "(" in v and p_start_idx == 0:
            p_start_idx = i
        if ")" in v and p_end_idx == -1:
            p_end_idx = i
    temp_list = temp_list[:p_start_idx] + temp_list[p_end_idx + 1 :]

    for i, v in enumerate(temp_list[:-1]):
        if v.lower() in replace_list:
            temp_list[i] = "/"

    tstr = " ".join(temp_list)
    if len(tstr) < 21:
        return tstr

    for i, word in enumerate(temp_list):
        if word.lower() in special_words or word.isdigit():
            temp_list[i] = f" {word} "
            continue
        temp_list[i] = f"{word[0].upper()}"

    return "".join(temp_list).replace("/.", "/ ").replace("./", " /").strip()


def read_kml(f: str, conversion_file: str = "co2milx.txt") -> tuple:
    ns = "{http://www.opengis.net/kml/2.2}"
    tree = ET.parse(f, parser=ET.XMLParser(encoding="utf-8", recover=True))
    root = tree.getroot()

    layer_name = root.find(f"{ns}Document/{ns}name").text.strip()
    hostile_modifier = "H" if layer_name == "Intel" else "F"

    raw_placemarks = list(filter(lambda x: "Placemark" in str(x), root.iter()))
    placemarks = []

    for p in raw_placemarks:
        s = list(map(lambda x: str(x).replace(ns, ""), list(p)))
        t = list(filter(lambda x: "LineString" in x, s))
        if len(t) == 0:
            placemarks.append(p)

    # Search for co2milx.txt in script dir, current working dir, or KML dir
    conv_candidates = [
        conversion_file,
        os.path.join(SCRIPT_DIR, conversion_file),
        os.path.join(os.path.dirname(os.path.abspath(f)), conversion_file),
    ]
    conv_path = next((p for p in conv_candidates if os.path.exists(p)), None)
    if not conv_path:
        raise FileNotFoundError(
            f"Could not find '{conversion_file}' in {SCRIPT_DIR} or {os.getcwd()}"
        )

    types = {}
    with open(conv_path, "r", encoding="utf-8") as cf:
        data = cf.read().strip().replace("\r", "").split("\n")
        data = list(filter(lambda x: not x.startswith("!!") and len(x) > 0, data))
        for row in data:
            c_idx = row.find("!")
            if c_idx != -1:
                row = row[0:c_idx]
            if ":" in row:
                k, v = row.strip().split(":", 1)
                types[k.strip()] = v.strip()

    sizes = {
        "troop": "D", "pl": "D", "squadron": "E", "coy": "F",
        "battery": "E", "bn": "F", "regiment": "G", "bde": "H",
        "div": "I", "corps": "J", "army": "K", "na": "-",
    }

    hostile_modifier_idx = 1
    size_modifier_idx = 11

    name_ignore_list = ["the", "own", "of", "royal", "bn", "regiment", "de", "la", "and"]
    replace_list = ["coy", "company", "bn", "pl", "platoon", "squadron", "sqn"]
    num_replace_list = ["1st", "2nd", "3rd", "4th", "5th", "6th", "7th", "8th", "9th", "0th", "2th", "3th"]
    special_words = ["mortar", "at", "base", "trains"]

    units = []
    for p in placemarks:
        uname = p.find(f"{ns}name").text.strip()
        location = p.find(f"{ns}Point")[0].text.strip().split(",")

        usuperior = ""
        usize = "na"
        utype_text = ""

        extended_data = p.find(f"{ns}ExtendedData")
        if extended_data is not None:
            superior_data = extended_data.find(f"{ns}Data[@name='superior']")
            if superior_data is not None and len(superior_data) > 0 and superior_data[0].text:
                usuperior = superior_data[0].text.strip()

            size_data = extended_data.find(f"{ns}Data[@name='size']")
            if size_data is not None and len(size_data) > 0 and size_data[0].text:
                usize = size_data[0].text.strip().lower()

            t_data = extended_data.find(f"{ns}Data[@name='type']")
            sub_data = extended_data.find(f"{ns}Data[@name='subtype']")
            if t_data is not None and sub_data is not None:
                t_txt = t_data[0].text.lower().strip() if t_data[0].text else ""
                sub_txt = sub_data[0].text.lower().strip() if sub_data[0].text else ""
                utype_text = f"{t_txt},{sub_txt}"

        if utype_text in types:
            utype = list(types[utype_text])
        else:
            print(f"[WARNING] Unmapped unit type '{utype_text}', using default infantry symbol.")
            utype = list("SFGPUCI--------")

        utype[hostile_modifier_idx] = hostile_modifier
        utype[size_modifier_idx] = sizes.get(usize, "-")

        # Strip quotes even on short names
        uname = uname.replace('"', "").replace("'", "")
        usuperior = usuperior.replace('"', "").replace("'", "")

        if len(uname) > 21:
            for num in num_replace_list:
                uname = uname.replace(num, num[0])
            uname = create_acronym(uname, name_ignore_list, replace_list, special_words)

        if len(usuperior) > 21:
            for num in num_replace_list:
                usuperior = usuperior.replace(num, num[0])
            usuperior = create_acronym(usuperior, name_ignore_list, replace_list, special_words)

        unit = {
            "name": uname,
            "superior": usuperior,
            "type": "".join(utype),
            "location": location,
        }
        units.append(unit)

    return layer_name, units


def write_to_milx(layer_name: str, units: list, outfile: str) -> None:
    ns = {
        None: "http://gs-soft.com/MilX/V3.1",
        "xsi": "http://www.w3.org/2001/XMLSchema-instance",
    }
    doclayer = ET.Element("MilXDocument_Layer", nsmap=ns)
    libver = ET.SubElement(doclayer, "MssLibraryVersionTag")
    libver.text = "2025.02.20"

    milx = ET.SubElement(doclayer, "MilXLayer")
    ET.SubElement(milx, "Name").text = layer_name
    ET.SubElement(milx, "LayerType").text = "Normal"
    gl = ET.SubElement(milx, "GraphicList")

    for unit in units:
        graphic = ET.SubElement(gl, "MilXGraphic")
        mss = ET.SubElement(graphic, "MssStringXML")

        safe_sup = xml_escape(unit["superior"], {'"': "&quot;", "'": "&apos;"})
        safe_name = xml_escape(unit["name"], {'"': "&quot;", "'": "&apos;"})

        attrs = [
            f'<Symbol ID="{unit["type"]}">',
            f'<Attribute ID="M">{safe_sup}</Attribute>',
            f'<Attribute ID="T">{safe_name}</Attribute>',
            "</Symbol>",
        ]
        mss.text = "".join(attrs)

        pl = ET.SubElement(graphic, "PointList")
        pt = ET.SubElement(pl, "Point")
        ET.SubElement(pt, "X").text = unit["location"][0].strip()
        ET.SubElement(pt, "Y").text = unit["location"][1].strip()

        syscust = ET.SubElement(graphic, "SysCustPropList")
        ET.SubElement(
            syscust,
            "CustProp",
            SystemID="gs-soft_ma",
            Name="SDZ",
            DataType="dt_string",
            Value="",
        )

    ET.SubElement(milx, "CoordSystemType").text = "WGS84"
    ET.SubElement(milx, "ViewScale").text = "0.1"
    ET.SubElement(milx, "SymbolSize").text = "1"

    dump = ET.tostring(
        doclayer,
        xml_declaration=True,
        encoding="UTF-8",
        pretty_print=True,
        standalone=False,
    )
    with open(outfile, "wb") as f:
        f.write(dump)


def tkinter_loop():
    root = tk.Tk()
    root.title("KML to MilXLY Converter")
    root.geometry("540x520")
    root.minsize(520, 500)

    style = ttk.Style()
    style.theme_use("clam")

    gamedir_var = tk.StringVar(value=r"D:\SteamLibrary\steamapps\common\Command Ops 2")
    infile_var = tk.StringVar()
    outfile_var = tk.StringVar()

    x1_var = tk.DoubleVar(value=0)
    y1_var = tk.DoubleVar(value=0)
    x2_var = tk.DoubleVar(value=0)
    y2_var = tk.DoubleVar(value=0)

    lat1_var = tk.DoubleVar(value=0)
    lon1_var = tk.DoubleVar(value=0)
    lat2_var = tk.DoubleVar(value=0)
    lon2_var = tk.DoubleVar(value=0)

    def browse_gamedir():
        dirname = filedialog.askdirectory(title="Select Command Ops 2 Directory")
        if dirname:
            gamedir_var.set(dirname)

    def browse_infile():
        saved_dir = os.path.join(gamedir_var.get(), "Saved Games")
        initial_dir = saved_dir if os.path.exists(saved_dir) else gamedir_var.get()
        filename = filedialog.askopenfilename(
            title="Select CO2 game save file or KML",
            initialdir=initial_dir,
            filetypes=[("CO2 Save / KML", "*.cog *.kml"), ("All Files", "*.*")]
        )
        if filename:
            infile_var.set(filename)
            if not outfile_var.get():
                base, _ = os.path.splitext(filename)
                outfile_var.set(base + ".milxly")

    def browse_outfile():
        filename = filedialog.asksaveasfilename(
            title="Save MilXLY File As",
            defaultextension=".milxly",
            filetypes=[("MilXLY Files", "*.milxly"), ("All Files", "*.*")]
        )
        if filename:
            outfile_var.set(filename)

    def run_conversion():
        game_dir = gamedir_var.get().strip()
        infile = infile_var.get().strip()
        outfile = outfile_var.get().strip()

        if not infile or not outfile:
            messagebox.showerror("Error", "Please fill in the Input file and Output path.")
            return

        try:
            # Allow direct KML input OR .cog savefile input
            if infile.lower().endswith(".kml"):
                kmls = [infile]
            else:
                calib_data = {
                    "x1": round(x1_var.get()), "y1": round(y1_var.get()),
                    "x2": round(x2_var.get()), "y2": round(y2_var.get()),
                    "lat1": lat1_var.get(), "lon1": lon1_var.get(),
                    "lat2": lat2_var.get(), "lon2": lon2_var.get(),
                }
                xy1 = [calib_data["x1"], calib_data["y1"]]
                xy2 = [calib_data["x2"], calib_data["y2"]]
                ll1 = [calib_data["lat1"], calib_data["lon1"]]
                ll2 = [calib_data["lat2"], calib_data["lon2"]]
                kmls = generate_kml(game_dir, infile, xy1, xy2, ll1, ll2)

            if not kmls:
                messagebox.showwarning("Warning", "No KML files were generated.")
                return

            written_files = []
            for kml in kmls:
                layer_name, units = read_kml(kml)
                pretty_print(units)
                target_out = outfile
                if len(kmls) > 1:
                    base, ext = os.path.splitext(outfile)
                    suffix = ".Friendly" if "Friendly" in kml else ".Intel"
                    target_out = f"{base}{suffix}{ext}"
                write_to_milx(layer_name, units, target_out)
                written_files.append(target_out)

            files_msg = "\n".join(written_files)
            messagebox.showinfo("Success", f"Successfully converted!\n\nFiles written:\n{files_msg}")
            root.destroy()
        except Exception as e:
            traceback.print_exc()
            messagebox.showerror("Conversion Error", str(e))

    # Layout
    main_frame = ttk.Frame(root, padding="15")
    main_frame.pack(fill=tk.BOTH, expand=True)

    file_frame = ttk.LabelFrame(main_frame, text=" File & Directory Paths ", padding="10")
    file_frame.pack(fill=tk.X, padx=5, pady=5)

    ttk.Label(file_frame, text="Game Directory:").grid(row=0, column=0, sticky=tk.W, pady=3)
    ttk.Entry(file_frame, textvariable=gamedir_var, width=38).grid(row=0, column=1, padx=5, pady=3)
    ttk.Button(file_frame, text="Browse...", command=browse_gamedir).grid(row=0, column=2, pady=3)

    ttk.Label(file_frame, text="Input (.cog/.kml):").grid(row=1, column=0, sticky=tk.W, pady=3)
    ttk.Entry(file_frame, textvariable=infile_var, width=38).grid(row=1, column=1, padx=5, pady=3)
    ttk.Button(file_frame, text="Browse...", command=browse_infile).grid(row=1, column=2, pady=3)

    ttk.Label(file_frame, text="Output MilXLY:").grid(row=2, column=0, sticky=tk.W, pady=3)
    ttk.Entry(file_frame, textvariable=outfile_var, width=38).grid(row=2, column=1, padx=5, pady=3)
    ttk.Button(file_frame, text="Browse...", command=browse_outfile).grid(row=2, column=2, pady=3)

    coord_frame = ttk.LabelFrame(main_frame, text=" Coordinate Calibration / Bounding Box ", padding="10")
    coord_frame.pack(fill=tk.X, padx=5, pady=10)

    ttk.Label(coord_frame, text="Point 1 - X1:").grid(row=0, column=0, sticky=tk.W, padx=2, pady=3)
    ttk.Entry(coord_frame, textvariable=x1_var, width=8).grid(row=0, column=1, padx=2, pady=3)
    ttk.Label(coord_frame, text="Y1:").grid(row=0, column=2, sticky=tk.W, padx=2, pady=3)
    ttk.Entry(coord_frame, textvariable=y1_var, width=8).grid(row=0, column=3, padx=2, pady=3)

    ttk.Label(coord_frame, text="Lat1:").grid(row=0, column=4, sticky=tk.W, padx=2, pady=3)
    ttk.Entry(coord_frame, textvariable=lat1_var, width=9).grid(row=0, column=5, padx=2, pady=3)
    ttk.Label(coord_frame, text="Lon1:").grid(row=0, column=6, sticky=tk.W, padx=2, pady=3)
    ttk.Entry(coord_frame, textvariable=lon1_var, width=9).grid(row=0, column=7, padx=2, pady=3)

    ttk.Label(coord_frame, text="Point 2 - X2:").grid(row=1, column=0, sticky=tk.W, padx=2, pady=3)
    ttk.Entry(coord_frame, textvariable=x2_var, width=8).grid(row=1, column=1, padx=2, pady=3)
    ttk.Label(coord_frame, text="Y2:").grid(row=1, column=2, sticky=tk.W, padx=2, pady=3)
    ttk.Entry(coord_frame, textvariable=y2_var, width=8).grid(row=1, column=3, padx=2, pady=3)

    ttk.Label(coord_frame, text="Lat2:").grid(row=1, column=4, sticky=tk.W, padx=2, pady=3)
    ttk.Entry(coord_frame, textvariable=lat2_var, width=9).grid(row=1, column=5, padx=2, pady=3)
    ttk.Label(coord_frame, text="Lon2:").grid(row=1, column=6, sticky=tk.W, padx=2, pady=3)
    ttk.Entry(coord_frame, textvariable=lon2_var, width=9).grid(row=1, column=7, padx=2, pady=3)

    btn_frame = ttk.Frame(main_frame)
    btn_frame.pack(fill=tk.X, padx=5, pady=10)

    ttk.Button(btn_frame, text="Convert to MilXLY", command=run_conversion).pack(side=tk.RIGHT, padx=5)
    ttk.Button(btn_frame, text="Cancel", command=root.destroy).pack(side=tk.RIGHT, padx=5)

    root.mainloop()


if __name__ == "__main__":
    if len(sys.argv) >= 3:
        try:
            _, infile, outfile = sys.argv
            layer_name, units = read_kml(infile)
            pretty_print(units)
            write_to_milx(layer_name, units, outfile)
            print(f"[SUCCESS] Converted {infile} to {outfile}")
        except Exception as e:
            print(f"---\n[ERROR] {e}\n---")
            sys.exit(1)
    else:
        tkinter_loop()
