"""
DATE
  26.04.25

DESCRIPTION
  This module covers the functionalities to convert
  a KML file generated from Command Ops 2's excellent
  GameStateExporter to a milxly XML file.

  The tool works in three steps:
    * Get all the relevant unit data from the KML file 
      for each unit(unit size, name, superior, ...)
    * Read the relevant definitions file(co2milx.txt),
      which is human readable, which has definitions for
      CO2 unit type -> MilX unit type. Basic units are 
      supported at this point.
    * For each Co2 unit, generate a XML entry in the output
      MilX file with the proper MilX unit type, name,
      superior, size and additional attributes(i.e HQ, task-force)
"""

import sys
from lxml import etree as ET

def pretty_print(l):
  for k in l:
    print(f" --- {k['name']} --- ")
    print(f"Superior: {k['superior']:<20}")
    print(f"Type: {k['type']:<20}")
    print(f"Location: {str(k['location']):<20}\n")

def create_acronym(name: str, ignore_list: list, replace_list: str) -> str:
  # Get the words in the ignore list out of the name
  temp_list = list(filter(
    lambda x: x.lower() not in ignore_list and\
      '(' not in x and ')' not in x,
    name.split()))
  # Replace things like "A Company Northshore Regiment"
  # with A / Northshore Regiment
  for i, v in enumerate(temp_list[:-1]):
    if v.lower() in replace_list:
        temp_list[i] = "/"

  # Check if the string can now fit within 21 characters,
  # if not, we'll only take the numbers + first characters
  tstr = " ".join(temp_list)
  if len(tstr) < 21:
    return tstr
  # If we're abbreviating, then add "." for words
  return "".join([f"{w[0]}." if not w.isdigit() else f"{w} " for w in temp_list]).replace("/.", "/ ").replace("./", " /")

def read_kml(f: str, conversion_file: str="co2milx.txt") -> dict:
  """Given a KML file F, read
  all the units exported by the Command Ops 2
  GameStatExporter, and then figure out the details
  of each unit according to MilX notations.

  The CONVERSION_FILE contains rulesets to convert
  between CO2 units and MilX units.

  Returns the layer name and the units in that layer.
  """
  ns = "{http://www.opengis.net/kml/2.2}"
  tree = ET.parse(f, 
                  parser=ET.XMLParser(encoding="utf-8", recover=True))
  root = tree.getroot()

  layer_name = root.find(f"{ns}Document/{ns}name").text.strip()
  hostile_modifier = "H" if layer_name == "Intel" \
    else "F"

  raw_placemarks = list(filter(lambda x: "Placemark" in str(x)
                      , root.iter()))
  placemarks = []

  # ignore all line sketches/subordinate
  # lines, etc
  for p in raw_placemarks:
    s = list(map(lambda x: str(x).replace(ns, ""),list(p)))
    t = list(filter(lambda x: "LineString" in x, s))
    if len(t) == 0:
      placemarks.append(p)

  # read the MilX notations from file
  types = {}
  with open(conversion_file, "r") as f:
    data = f.read().strip().replace("\r", "").split("\n")
    data = list(filter(lambda x: not x.startswith("!!")\
                        and len(x) > 0, data))
    for row in data:
      k,v = row.strip().split(':')
      types[k.strip()] = v.strip()

  sizes = {
    "troop": "D",
    "pl": "D",
    "squadron": "E",
    "coy": "F",
    "battery": "E",
    "bn": "F",
    "regiment": "G",
    "bde": "H",
    "div": "I",
    "corps": "J",
    "army": "K",
    "na": "-"
  }

  # based on the size, alignment and type of unit,
  # we will edit the specific index describing
  # the unit metadata.
  hostile_modifier_idx = 1
  size_modifier_idx = 11
  
  # For concatenation of unit names, if bigger than
  # a certain length, we must ignore these common
  # words, and clean out the unit name for effiecient
  # abbreviation.
  name_ignore_list = ["the", "own", "of", "royal", "bn", "regiment",
                      "de", "la"]
  replace_list = ["coy", "company", "bn", "regiment", "pl", "platoon",
                  "squadron", "sqn"]
  num_replace_list = ["1st", "2nd", "3rd", "4th", "5th", "6th", "7th",
                      "8th", "9th", "0th", "2th", "3th"]

  units = []
  for p in placemarks:
    uname = p.find(f"{ns}name").text.strip()
    location = p.find(f"{ns}Point")[0].text.split(",")

    # Get the superior unit and size of this 
    # unit
    usuperior = ""
    usize = "na"
    utype_text = ""

    extended_data = p.find(f"{ns}ExtendedData")
    if extended_data is not None:
      superior_data = extended_data.find(f"{ns}Data[@name='superior']")
      if superior_data is not None:
        usuperior = superior_data[0].text.strip()
      usize = extended_data.find(f"{ns}Data[@name='size']")
      if usize is not None:
        usize = usize[0].text.strip().lower()
      utype_text = extended_data.find(f"{ns}Data[@name='type']")
      subtype = extended_data.find(f"{ns}Data[@name='subtype']")
      if utype_text is not None:
        utype_text = f"{utype_text[0].text.lower().strip()},{subtype[0].text.lower().strip()}"
        
    # Convert the type into list gained from the 
    # XML file.
    utype: list = [x for x in types[utype_text]]
    utype[hostile_modifier_idx] = hostile_modifier
    utype[size_modifier_idx] = sizes[usize]

    # do final checks
    # MilX has a name length limit of 21
    # characters, so we have to do a concatenation.
    if len(uname) > 21:
      for num in num_replace_list:
        uname = uname.replace(num, num[0])
      uname = create_acronym(uname, name_ignore_list, replace_list)

    if len(usuperior) > 21:
      for num in num_replace_list:
        usuperior = usuperior.replace(num, num[0])
      usuperior = create_acronym(usuperior, name_ignore_list, replace_list)


    unit = {}
    unit["name"] = uname
    unit["superior"] = usuperior
    unit["type"] = "".join(utype)
    unit["location"] = location
    units.append(unit)

  return layer_name, units

def write_to_milx(layer_name: str, units: list, outfile: str) -> None:
  """Given a LAYER_NAME, along with a collection of UNITS,
  this function generates a MilX/map.army compatible OUTFILE.
  """
  ns = {
    None: "http://gs-soft.com/MilX/V3.1",
    "xsi": "http://www.w3.org/2001/XMLSchema-instance"
  }
  doclayer = ET.Element("MilXDocument_Layer", nsmap=ns)
  libver = ET.SubElement(doclayer, "MssLibraryVersionTag")
  libver.text = "2025.02.20"

  # delcare the headers and data trees
  milx = ET.SubElement(doclayer, "MilXLayer")
  ET.SubElement(milx, "Name").text = layer_name
  ET.SubElement(milx, "LayerType").text = "Normal"
  gl = ET.SubElement(milx, "GraphicList")

  # add the actual units
  for unit in units:
    graphic = ET.SubElement(gl, "MilXGraphic")
    mss = ET.SubElement(graphic, "MssStringXML")
    attrs = [
      f"<Symbol ID=\"{unit['type']}\">",
      f"<Attribute ID=\"M\">{unit['superior']}</Attribute>",
      f"<Attribute ID=\"T\">{unit['name']}</Attribute>",
      "</Symbol>",
    ]
    mss.text = "".join(attrs)

    pl = ET.SubElement(graphic, "PointList")
    pt = ET.SubElement(pl, "Point")
    ET.SubElement(pt, "X").text = unit["location"][0]
    ET.SubElement(pt, "Y").text = unit["location"][1]

    syscust = ET.SubElement(graphic, "SysCustPropList")
    ET.SubElement(syscust, "CustProp", 
                  SystemID="gs-soft_ma", Name="SDZ",
                  DataType="dt_string", Value="")

  # add the rest of the metadata
  ET.SubElement(milx, "CoordSystemType").text = "WGS84"
  ET.SubElement(milx, "ViewScale").text = "0.1"
  ET.SubElement(milx, "SymbolSize").text = "1"

  dump = ET.tostring(doclayer, xml_declaration=True, encoding="UTF-8", pretty_print=True, standalone=False)
  with open(outfile, "wb") as f:
    f.write(dump)


htext = """
NAME
  kml2milxly

DESCRIPTION
  A tool for converting GameStatExporter's KML output
  from command ops 2 game state to map.army style MilX
  layer.

USAGE
  [infile], [outfile]

EXAMPLES
  python ./kml2milxly.py friendly.kml out.milxly 
"""

if __name__ == "__main__":
  if len(sys.argv) < 3:
    print(htext)

  _, infile, outfile = \
    sys.argv

  try:
    layer_name, units = read_kml(infile)
    pretty_print(units)
    write_to_milx(layer_name, units, outfile)
  except:
    print(htext)
