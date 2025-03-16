##
# Visualizes the structure of a Live Home 3D Pro Project.
#
# This script can be run on a `project.xml` file extracted from a Live Home 3D Pro (LH3DP) project
# file (`.lhzd`, which is just a ZIP archive) to see an ASCII tree visualization of the objects in
# the project.
#
# This is useful because the UI of LH3DP has a limit on how many characters it will show in the
# "Project Tree" sidebar. It can be used to identify any inconsistencies in the naming of objects
# before exporting them to FBX for processing in Blender.
# ==================================================================================================
# Copyright (C) 2025 Guy Elsmore-Paddock
#
# This program is free software: you can redistribute it and/or modify it under the terms of the GNU
# Affero General Public License as published by the Free Software Foundation, either version 3 of
# the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without
# even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
# Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public License along with this program.
# If not, see <http://www.gnu.org/licenses/>.
#

import xml.etree.ElementTree as ET
from collections import defaultdict

EXCLUDED_CLASSES = {"Measurement", "UserCamera", "Camera", "MovieTrack"}


def parse_element(element, level=0, parent_map=None):
    """Recursively parse elements and format them as an ASCII tree."""
    name = element.get("customName") or f"Unnamed {element.get('class', 'Unknown')}"
    class_name = element.get("class", "Unknown")

    if class_name in EXCLUDED_CLASSES:
        return ""

    indent = "  " * level + ("└─" if level > 0 else "")
    tree_str = f"{indent}{name} ({class_name})\n"
    child_indent = "  " * (level + 1) + "└─"

    # Handle mouldings inside walls
    if class_name == "Wall":
        mouldings = element.find("mouldings")
        if mouldings is not None:
            for moulding in sorted(mouldings.findall("*"), key=lambda e: e.get("customName", "")):
                moulding_name = moulding.get("customName", "Unnamed Moulding")
                tree_str += f"{child_indent}{moulding_name} (Moulding)\n"

    # Handle roof sides inside roofs
    if class_name == "Roof":
        roof_products = element.find("products")
        if roof_products is not None:
            for roof_side in sorted(roof_products.findall("*[@class='RoofSide']"),
                                    key=lambda e: e.get("customName", "")):
                roof_side_name = roof_side.get("customName", "Unnamed RoofSide")
                tree_str += f"{child_indent}{roof_side_name} (RoofSide)\n"

    # Process other children normally
    children = sorted(parent_map.get(element, []), key=lambda e: e.get("customName", ""))
    for child in children:
        tree_str += parse_element(child, level + 1, parent_map)

    return tree_str


def generate_ascii_tree(xml_path):
    """Generate an ASCII tree from a LiveHome 3D Pro XML file."""
    tree = ET.parse(xml_path)
    root = tree.getroot()
    
    # Build a parent-child map
    parent_map = defaultdict(list)
    storeys = []

    for element in root.findall(".//products/*[@class]"):
        class_name = element.get("class")
        parent = element.find("..")
        if parent is not None and "class" in parent.attrib:
            parent_map[parent].append(element)
        if class_name == "BuildingStorey":
            storeys.append(element)

    # Ensure storeys capture their respective walls, slabs, and roofs
    output = ""
    for storey in sorted(storeys, key=lambda e: e.get("customName", "")):
        output += parse_element(storey, 0, parent_map)
        products = storey.find("products")
        if products is not None:
            children = sorted(products.findall("*[@class]"), key=lambda e: e.get("customName", ""))
            for child in children:
                output += parse_element(child, 1, parent_map)

    return output


if __name__ == "__main__":
    xml_file = "project.xml"  # Update this path if necessary
    tree_output = generate_ascii_tree(xml_file)
    print(tree_output)
