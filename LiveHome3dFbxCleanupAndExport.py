##
# This script can be run in Blender to re-arrange and clean-up an FBX model from Live Home 3D Pro
# so that it's more suitable for use in Unreal Engine 4/5.
#
# All objects in Live Home 3D should follow a naming convention similar to UE4 naming conventions:
#
#   SM_<Room Name>_<Element Type>
#
# For example:
#   SM_BackPorch_Ceiling
#   SM_BackPorch_Floor
#   SM_BackPorch_Wall_01
#   SM_BackPorch_Wall_01_Moulding_Base_Left
#   SM_BackPorch_Wall_01_Moulding_Crown_Left
#   SM_BackPorch_Wall_01_Window_01
#   SM_BackPorch_Wall_01_Window_01_Opening
#   SM_BackPorch_Wall_01_Window_02
#   SM_BackPorch_Wall_01_Window_02_Opening
#   SM_BackStairwell_Roof
#   SM_BackStairwell_Roof_Gable_01
#   SM_BackStairwell_Roof_Hole_01
#   SM_BackStairwell_Roof_SegmentedSide_01
#
# Live Home 3D adds a variable-length, random string of characters to the end of every object during
# export. So, the raw export from Live Home 3D will contain objects with names like the following
# (and the random string changes during each export):
#
#   SM_BackPorch_Ceiling_0c_n7s8x13_eOFCzcBLIak
#   SM_BackPorch_Floor_3oXO8swYvCdvboc6Q8Uv7T
#   SM_BackPorch_Wall_01_0o68zbOCH29OnTp2cQRU9r
#   SM_BackPorch_Wall_01_Moulding_Base_Left_1J28pxPYP5IxjbvlKfy$8j
#   SM_BackPorch_Wall_01_Moulding_Crown_Left_3h55DlIhL1MPxJBXH7QEhi
#   SM_BackPorch_Wall_01_Window_01_3baVCV2oL6ZR8S5RsEs8e3
#   SM_BackPorch_Wall_01_Window_01_Opening_3NNYrtBLj4IuQQHSklD4i3
#   SM_BackPorch_Wall_01_Window_02_0yhmf4cwv2Du5PP8UdTVLr
#   SM_BackPorch_Wall_01_Window_02_Opening_2OKoaY1vbFC8lyUCdFFxML
#   SM_BackStairwell_Roof_0eGH9cb21EEA36BeUuc3Gk
#   SM_BackStairwell_Roof_Gable_01_0QTot$NVLAt9loQGf4NnNS
#   SM_BackStairwell_Roof_Hole_01_1qfzoO5oP0TP7rkivGdnv5
#   SM_BackStairwell_Roof_SegmentedSide_01_3aeIOLKYL9fOZSqIxV$Mkl
#
# This script will strip off those random characters and organize all the pieces of the house into
# collections by room and element. For example, the following collections would be created from the
# objects listed in the example above:
#   - SM_BackPorch_Ceiling
#   - SM_BackPorch_Floor
#   - SM_BackPorch_Wall_01
#   - SM_BackStairwell_Roof
#
# This script will perform the following steps:
#   1. Remove all objects that are not meshes (including parent objects).
#   2. Fix-up the naming of "Slab" objects that Live Home 3D generates itself, since these objects
#      cannot be renamed inside Live Home 3D itself.
#   3. Organize objects into collections by room and element.
#   4. Adjusts the position of the house model so that its center on the X and Y axes matches the
#      origin of the world.
#   5. Converts triangles to quads and eliminates split normals (in case there are any; generally
#      this doesn't seem to be the case with LH3D exports).
#   6. Generates a secondary UV map for UE4 lighting, so that UE does not encounter overlapping UVs
#      during lightmap generation.
#   7. Re-generates the primary UV map using cube projection so that the UVs are more reasonable and
#      applying materials to walls in UE doesn't end up looking like a ransom note or hodgepodge of
#      text pieces.
#   8. (Optionally) Applies Blender's UV checkboard test pattern texture to all meshes so that it's
#      easy to spot problems with the mesh UVs while in Blender.
#   9. Generates basic convex hull collision for all posts, walls, and stairs using remesh and a
#      convex hull decomposition algorithm.
#  10. Generates complex collision for slabs (ceilings/floors) using remesh and a convex hull
#      decomposition algorithm.
#  11. Exports each collection of meshes as separate FBX files in the same folder where the Blender
#      project file has been saved.
#
# Dependencies:
#   - Blender 4.2+.
#   - Object: Bool Tool (https://extensions.blender.org/add-ons/bool-tool/) plug-in enabled.
#   - Convex Decomposition plug-in (https://github.com/olitheolix/blender-convex-decomposition)
#     enabled.
# ==================================================================================================
# Copyright (C) 2021-2025 Guy Elsmore-Paddock
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

import bmesh
import bpy
import re
import sys
import time

from collections import OrderedDict, defaultdict
from math import radians
from mathutils import Vector
from mathutils.bvhtree import BVHTree
from pathlib import Path

fbx_path = r"C:\PATH\TO\LIVE\HOME\Export.fbx"

# The center of the scene is normally calculated as the center of volume. If you need the center of
# the scene to be constant from import to import (e.g., for revising the same LH 3D scene), you can
# uncomment the second line below and set it to a specific point in the scene. This point will be
# shifted to be the origin (0, 0, 0) for exports.
fbx_fixed_scene_center = None
# fbx_fixed_scene_center = Vector((0.0, 0.0, 0.0))
# fbx_fixed_scene_center = Vector((32.76048278808594 - 0.05441, 48.72707748413086 + 0.09118, 3.8340983390808105))

element_regex_str = \
    (r"^SM_(?P<Room>(?:[^_]+))"
     r"_"
     r"(?P<Element>(?:"
     r"(?:(?:Conduit(?:_\d{2})?_)?(?:Closet_)?)"
     r"(?:CeilingTrim"
     r"|Ceiling(?:_\d{2})?"
     r"|Floor(?:_\d{2}_Slab)?"
     r"|(?:Stair)?Wall_\d{2}(?:_(?:(?:Moulding_(?:Base|Crown)_(?:Left|Right))"
     r"|(?:Garden)?Window(?:_\d{2})?(?:_Opening)?"
     r"|Door_\d{2}(?:_Opening)?"
     r"|Opening(?:_\d{2})?))?"
     r"|WallPanel(?:_\d{2})?"
     r"|Roof(?:_\d{2})?(?:_(?:Gable|Hole|Side|SegmentedSide|Vent)(?:_\d{2})?)?(?:_Window_\d{2}(?:_Opening)?)?"
     r"|Post(?:_\d{2})?"
     r"|Stairs(?:_Opening)?(?:_\d{2})?"
     r"|Conduit"
     r"|Tub_Shelf))"
     r"(?:_Placeholder(?:_\d{2})?)?)?"
     r"(?P<Garbage>_.*)?$")

# Uncomment the second line and customize it to debug processing with just a subset of the geometry.
unwanted_element_regex_str = r"^.+((_(Door|Window)_\d{2})|(Placeholder.*))$"
# unwanted_element_regex_str = "^((?!(.*_Floor_02|(Hallway|ScottRoom)_Floor|.*Stairs_Opening.*)).*)|(.+((_(Door|Window)_\d{2})|(Placeholder.*)))$"
# unwanted_element_regex_str = "^((?!(.*Stairs_Opening.*|.*_02_Slab)).*)|(.+((_(Door|Window)_\d{2})|(Placeholder.*)))$"

prefix_regex_str = \
    r"^(?P<Prefix>(?:Closet_)?(?:Conduit(?:_\d{2})?_)?" \
    r"(?:CeilingTrim|Ceiling|Floor|Post|Roof|Slab|StairWall|Stairs|Tub_Shelf" \
    r"|WallPanel|Wall)(?:_\d{2})?)"

# All elements matched by this regex are UV-mapped as though they were a single object.
#
# - Slabs are included in this pattern because the sides of slabs need to line up with exterior walls.
# - Door openings are included in this pattern to ensure that floors that are adjacent to door openings line up for
#   textures like hardwood floors.
continuous_uv_regex_str = \
    r"^.+_(?:(?:Wall|StairWall|Roof(?:_\d{2})?_(Gable|Side|SegmentedSide)|Ceiling|Floor|Slab)(?:_\d{2})?)" \
    r"(?:(?:_Door(?:_\d{2})?_Opening)?|_Opening(?:_\d{2})?)$"

# Ceilings are in this list because the player might jump up in a low area (e.g., a porch).
# Meanwhile, roof gables are handled like walls, so they're in the basic collision list. The rest of
# a roof can be handled in a much simpler way since it can't have openings for doors and windows.
basic_collision_regex_str = r"^.+_(?:(?:Wall|Post|StairWall|Roof(?:_\d{2})?_Gable)(?:_\d{2})?)$"
roof_collision_regex_str = r"^.+_(?:Ceiling|(?:Roof(?:_\d{2})?_(?:Segmented)?Side)(?:_\d{2}))$"
slab_collision_regex_str = r"^House_Floor_\d{2}_Slab$"

wall_opening_regex_str = r"^$NAME$_(?:(Door|Window)_[0-9]{2}_)?Opening(?:_[0-9]{2})?$"
floor_opening_regex_str = r"^.+_Stairs_Opening(?:_\d{2})?$"
multipart_opening_regex_str = r"^(?P<Prefix>.+Opening)_(\d{2})$"

element_regex = re.compile(element_regex_str)
unwanted_element_regex = re.compile(unwanted_element_regex_str)
prefix_regex = re.compile(prefix_regex_str)

continuous_uv_regex = re.compile(continuous_uv_regex_str)

basic_collision_regex = re.compile(basic_collision_regex_str)
roof_collision_regex = re.compile(roof_collision_regex_str)
slab_collision_regex = re.compile(slab_collision_regex_str)

floor_opening_regex = re.compile(floor_opening_regex_str)
multipart_opening_regex = re.compile(multipart_opening_regex_str)


def import_fbx(path):
    bpy.ops.import_scene.fbx(filepath=path)
    repaint_screen()


def cleanup_scene():
    print("")
    print("=== Cleaning up the scene ===")

    remove_unwanted_objects_by_type()
    assign_slab_names()
    group_objects_by_room_and_type()
    remove_unwanted_objects_by_name()
    translate_origin_of_all_objects_to_world_origin()
    simplify_geometry()


def setup_uvs():
    generate_diffuse_uvs()
    generate_lightmap_uvs()


def generate_collision():
    print("")
    print("=== Generating collision ===")

    generate_roof_collision()
    generate_basic_collision()
    generate_slab_collision()


def export_all_collections_to_fbx():
    print("")
    print("=== Exporting scene to FBX ===")

    for coll in bpy.data.collections:
        status_print(f"  - Exporting collection '{coll.name}' to FBX...")

        # Select only objects in the current collection.
        deselect_all_objects()

        try:
            bpy.ops.export_scene.fbx(
                filepath=str(Path(bpy.data.filepath).parent / f"{coll.name}.fbx"),
                check_existing=False,
                collection=coll.name,
                object_types={'MESH'},
                use_mesh_modifiers=False,
                mesh_smooth_type='EDGE',
                use_tspace=True,
                add_leaf_bones=False,
                bake_anim=False,
            )

        except RuntimeError:
            print("FBX export error:", sys.exc_info()[0])

            # Pause to catch user's attention
            time.sleep(2)

    print("")


def remove_unwanted_objects_by_type():
    print("Removing unwanted, non-mesh objects...")

    meshes = [o for o in bpy.data.objects if o.type == 'MESH']
    non_meshes = [o for o in bpy.data.objects if o.type != 'MESH']

    for ob in meshes:
        print(f"  - Keeping '{ob.name}' (type '{ob.type}').")

    for ob in non_meshes:
        print(f"  - Deleting '{ob.name}' (type '{ob.type}').")

    # Remove the link between the meshes and their parents before we remove the
    # unwanted parent objects.
    with bpy.context.temp_override(selected_objects=meshes):
        bpy.ops.object.parent_clear(type='CLEAR_KEEP_TRANSFORM')

    with bpy.context.temp_override(selected_objects=non_meshes):
        bpy.ops.object.delete()

    repaint_screen()


def assign_slab_names():
    print("Assigning slabs names based on their position in Z Dimension...")

    slabs = {}
    slabs_min_z = {}

    for ob in bpy.data.objects:
        if ob.name.startswith('Slab'):
            slabs[ob.name] = ob

    for slab_ob in slabs.values():
        slab_min_z = 999999.0

        for vertex in slab_ob.data.vertices:
            v_world = slab_ob.matrix_world @ Vector(
                (vertex.co[0], vertex.co[1], vertex.co[2])
            )

            slab_min_z = min(slab_min_z, v_world[2])

        slabs_min_z[slab_ob.name] = slab_min_z

    sorted_slabs = OrderedDict(
        sorted(
            slabs_min_z.items(),
            key=lambda kv: kv[1]
        )
    )

    for slab_index, slab_name in enumerate(sorted_slabs.keys(), start=1):
        slabs[slab_name].name = "SM_House_Floor_%02d_Slab" % slab_index


def group_objects_by_room_and_type():
    print("Grouping meshes by room and type...")

    prefixes = []

    for ob in bpy.data.objects:
        element_match = element_regex.match(ob.name)

        if element_match is not None:
            room = element_match.group('Room')
            element = element_match.group('Element')
            garbage = element_match.group('Garbage')

            if element is not None:
                prefix_match = prefix_regex.match(element)

                if prefix_match is not None:
                    element_prefix = "_".join([
                        'SM',
                        room,
                        prefix_match.group('Prefix'),
                    ])

                    if element_prefix not in prefixes:
                        print(f"  - Creating collection prefix '{element_prefix}'.")
                        prefixes.append(element_prefix)

            if garbage is not None:
                new_name = ob.name.replace(garbage, '')
                print(f"  - Trimming garbage in name '{ob.name}' to '{new_name}'.")
                ob.name = new_name

    for ob in [o for o in bpy.data.objects if o.type == 'MESH']:
        for prefix in prefixes:
            if ob.name.startswith(prefix):
                print(f"  - Adding '{ob.name}' to collection prefix '{prefix}'.")

                # Remove static mesh prefix since it moved up to the collection and filename.
                ob.name = ob.name.replace('SM_', '')

                set_parent_collection(ob, prefix)


def remove_unwanted_objects_by_name():
    print("Removing unwanted objects by name...")

    unwanted_objects = [o for o in bpy.data.objects
                        if unwanted_element_regex.match(o.name)]

    for ob in unwanted_objects:
        print(f"  - Deleting '{ob.name}' (type '{ob.type}').")

    with bpy.context.temp_override(selected_objects=unwanted_objects):
        bpy.ops.object.delete()


def translate_origin_to_midpoint(ob):
    ob.select_set(True)
    bpy.ops.object.origin_set(type='ORIGIN_GEOMETRY', center='BOUNDS')


def translate_origin_to_world_origin(ob):
    ob.select_set(True)
    bpy.context.view_layer.objects.active = ob

    bpy.ops.transform.translate(value=(0, 0, 0), orient_type='GLOBAL')

    bpy.context.scene.cursor.location = Vector((0.0, 0.0, 0.0))

    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')


def translate_origin_of_all_objects_to_world_origin():
    print("Centering and resetting floor plan origin around world origin...")

    bpy.ops.object.select_by_type(type='MESH')

    # Center cursor to objects
    obs = bpy.context.selected_objects
    n = len(obs)
    assert n

    if fbx_fixed_scene_center is None:
        print("  - Calculating center of the scene...")
        scene_center = sum([o.matrix_world.translation for o in obs], Vector()) / n
        print(f"  - The center of the scene is: {scene_center.x}, {scene_center.y}, {scene_center.z}")
    else:
        scene_center = fbx_fixed_scene_center
        print(f"  - The center of the scene is: {scene_center.x}, {scene_center.y}, {scene_center.z} (set by constant)")

    cursor = bpy.context.scene.cursor
    cursor.location = scene_center
    cursor.location.z = 0

    # Move objects back to origin of scene
    for ob in bpy.data.objects:
        if bpy.data.objects.get(ob.name):
            status_print(f"  - Adjusting location of '{ob.name}' relative to cursor...")

            bpy.context.view_layer.objects.active = ob

            # Instances must be baked for us to shift origin properly.
            bpy.ops.object.make_single_user(
                object=True,
                obdata=True,
                material=False,
                animation=False
            )

            ob.location = ob.location - cursor.location

    print("")
    repaint_screen()

    # This doesn't properly snap instances but that might be ok for now
    cursor.location = (0, 0, 0)

    for ob in bpy.data.objects:
        bpy.context.view_layer.objects.active = ob

        status_print(f"  - Shifting origin of '{ob.name}' to world center using the cursor...")
        bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')

    repaint_screen()


def simplify_geometry():
    print("Simplifying model geometry...")

    for ob in [o for o in bpy.data.objects if o.type == 'MESH']:
        print(f"  - Simplifying '{ob.name}'...")

        deselect_all_objects()

        ob.select_set(True)
        bpy.context.view_layer.objects.active = ob

        bpy.ops.object.mode_set(mode='EDIT')
        bpy.ops.mesh.select_all(action='SELECT')

        bpy.ops.mesh.tris_convert_to_quads()
        bpy.ops.mesh.remove_doubles()
        bpy.ops.mesh.customdata_custom_splitnormals_clear()

    print("")
    deselect_all_objects()
    repaint_screen()


def shade_all_objects_flat():
    print("Changing shading of all models to 'Flat'...")

    for ob in [o for o in bpy.data.objects if o.type == 'MESH']:
        print(f"  - Changing shading of '{ob.name}'...")

        deselect_all_objects()

        ob.select_set(True)
        bpy.context.view_layer.objects.active = ob

        bpy.ops.object.shade_flat()

    print("")
    deselect_all_objects()
    repaint_screen()


def generate_diffuse_uvs():
    """
    Generates UVs for texturing (diffuse color) in Unreal Engine using cube projection.

    Prior to cube projection, objects for which UVs need to be continuous with those of their
    neighbors (e.g., walls, floors, ceilings, etc.) are joined into a single object. Once cube
    projection is complete, these objects are then split back into discrete objects that are placed
    back into their original collections. Blender doesn't have a native ability to retain this
     information, so this method relies on stashing the information in vertex groups.
    """
    uv_map_name = 'DiffuseUV'

    print("Generating primary UV for UE texturing on each mesh...")

    deselect_all_objects()

    # Find and join all objects requiring continuous UVs into a single object temporarily, so we can
    # project UVs that line up across adjacent objects.
    continuous_uv_objects = [
        o for o in bpy.data.objects
        if o.type == 'MESH' and continuous_uv_regex.match(o.name)
    ]

    continuous_uv_object_names_and_collections = [
        (ob.name, ob.users_collection[0].name) for ob in continuous_uv_objects
    ]

    print("  - Joining objects together for cube-projection of new UVs...")
    joined_ob = join_objects(continuous_uv_objects)

    # When multiple objects get joined, the new joined object takes on the name of the first object.
    # After the cube projection, we need to break up the joined object and restore the names, so we
    # need to rename the joined object.
    joined_ob_name = "temp_joined_continuous_objects"
    joined_ob.name = joined_ob_name

    # Project UVs onto all objects, including the continuous-UV ones.
    print("  - Cube-projecting new UVs on all objects...")
    deselect_all_objects()
    apply_uv_func(uv_map_name, box_uv_project)

    # Now, separate the walls back into separate objects so we can generate collection.
    # Each object name was used as a vertex group name before the objects were joined.
    for (object_name, collection_name) in continuous_uv_object_names_and_collections:
        status_print(f"  - Splitting vertex group '{object_name}' back out to object...")
        vertex_group = joined_ob.vertex_groups.get(object_name)

        if not vertex_group:
            raise KeyError(f"Could not locate vertex group: {object_name}")

        deselect_all_objects()
        joined_ob.select_set(True)

        bpy.ops.object.mode_set(mode='EDIT')

        # Select vertices belonging to this vertex group.
        joined_ob.vertex_groups.active = vertex_group

        # Deselect any vertices previously selected, then select ONLY this group's vertices.
        bpy.ops.mesh.select_all(action='DESELECT')
        bpy.ops.object.vertex_group_select()

        # Split the selection into a new object.
        bpy.ops.mesh.separate(type='SELECTED')
        bpy.ops.object.mode_set(mode='OBJECT')

        # Refresh the joined object (which is the active object) and grab the newly created object,
        # which is selected but not the active object.
        joined_ob = bpy.context.view_layer.objects.active
        split_ob = [ob for ob in bpy.context.selected_objects if ob.name != joined_ob.name][0]

        # Rename the new object back to its old name, then put it back in its old collection.
        split_ob.name = object_name
        set_parent_collection(split_ob, collection_name)

        # Remove all vertex groups from the new object
        for vertex_group_name_to_remove in split_ob.vertex_groups.keys():
            split_ob.vertex_groups.remove(split_ob.vertex_groups[vertex_group_name_to_remove])

    # Delete the temporary, joined object that is now empty.
    delete_object(joined_ob)

    print("")


def generate_lightmap_uvs():
    print("Generating secondary UV for UE light maps on each mesh...")

    uv_map_name = 'Lightmap'

    # deselect all to make sure select one at a time
    deselect_all_objects()

    apply_uv_func(uv_map_name, smart_uv_project)


def box_uv_project():
    bpy.ops.uv.cube_project(cube_size=1)


def smart_uv_project():
    bpy.ops.uv.smart_project(angle_limit=66, island_margin=0.02)


def apply_uv_func(uv_map_name, func):
    for ob in [o for o in bpy.data.objects if o.type == 'MESH']:
        status_print(f"  - Projecting {uv_map_name} for '{ob.name}'...")

        # From https://blender.stackexchange.com/a/120807
        ob.select_set(True)
        bpy.context.view_layer.objects.active = ob

        uv_map = ob.data.uv_layers.get(uv_map_name)

        if not uv_map:
            uv_map = ob.data.uv_layers.new(name=uv_map_name)

        uv_map.active = True

        bpy.ops.object.mode_set(mode='EDIT')
        bpy.ops.mesh.select_all(action='SELECT')
        func()

        bpy.ops.object.mode_set(mode='OBJECT')
        ob.select_set(False)

    print("")


def create_uv_grid_material(material_name):
    """Create a material with a UV grid texture."""
    image_name = "UV Grid"

    # Create the UV grid image if it doesn't already exist.
    if not bpy.data.images.get(image_name):
        bpy.ops.image.new(
            name=image_name,
            width=1024,
            height=1024,
            color=(0.0, 0.0, 0.0, 1.0),
            alpha=True,
            generated_type='UV_GRID',
            float=False
        )

    image = bpy.data.images.get(image_name)
    mat = bpy.data.materials.new(name=material_name)
    mat.use_nodes = True

    bsdf = mat.node_tree.nodes.get("Principled BSDF")
    if not bsdf:
        bsdf = mat.node_tree.nodes.new('ShaderNodeBsdfPrincipled')

    tex_image = mat.node_tree.nodes.new('ShaderNodeTexImage')
    tex_image.image = image

    mat.node_tree.links.new(
        bsdf.inputs['Base Color'],
        tex_image.outputs['Color']
    )

    return mat

def get_or_create_uv_grid_material(material_name, ob):
    """Gets or creates a material with a UV grid and adds it to the object."""
    mat = bpy.data.materials.get(material_name)

    if mat is None:
        mat = create_uv_grid_material(material_name)

    if mat.name not in [slot.name for slot in ob.data.materials]:
        ob.data.materials.append(mat)

    return ob.data.materials.keys().index(mat.name)

def assign_uv_grid_materials_by_object_face_normals(ob, angle_threshold=5):
    """Assigns unique instances of the UV grid material to faces based on their normal angles."""

    # Ensure the object has data to manipulate.
    if not ob.data.polygons:
        print("    - Warning: No faces found in the selected object.")
        return

    # Remove all existing material slots from the object.
    while ob.data.materials:
        ob.data.materials.pop(index=0)

    # Create a bmesh for easier face manipulation.
    bm = bmesh.new()
    bm.from_mesh(ob.data)

    # Normalize face normals and group faces by normal angles.
    bm.faces.ensure_lookup_table()
    grouped_faces = {}

    for face in bm.faces:
        face_normal = face.normal.normalized().freeze()
        matched_group = None

        if face_normal.length == 0:
            print(f"    - Warning: Face {face.index} has a zero-length normal and will be skipped.")
            continue

        for group_normal in grouped_faces.keys():
            if face_normal.angle(group_normal) <= radians(angle_threshold):
                matched_group = group_normal
                break

        if matched_group is not None:
            grouped_faces[matched_group].append(face)
        else:
            grouped_faces[face_normal] = [face]

    # Assign unique UV grid materials to each group
    for idx, (normal, faces) in enumerate(grouped_faces.items(), start=1):
        mat_name = f"UV_Grid_{idx:03}"
        mat_index = get_or_create_uv_grid_material(mat_name, ob)

        for face in faces:
            face.material_index = mat_index

    # Write back the changes to the mesh
    bm.to_mesh(ob.data)
    bm.free()
    print(f"    - {ob.name}: Assigned {len(grouped_faces)} unique materials based on face normals.")


def assign_unique_materials_by_face_normals():
    print("Applying UV grid test pattern to each mesh...")

    for ob in [o for o in bpy.data.objects if o.type == 'MESH']:
        print(f"  - Applying UV grid to '{ob.name}'...")

        deselect_all_objects()
        ob.select_set(True)
        bpy.context.view_layer.objects.active = ob

        assign_uv_grid_materials_by_object_face_normals(ob)

    print("")
    repaint_screen()


def generate_basic_collision():
    print("")
    print("Generating collision for simple objects...")

    collision_obs = [
        o for o in bpy.data.objects
        if o.type == 'MESH' and basic_collision_regex.match(o.name)
    ]

    for src_ob in collision_obs:
        status_print(f"  - Generating collision for '{src_ob.name}'...")

        deselect_all_objects()

        focus_on_object_in_viewport(src_ob)
        repaint_screen()

        # Create a temporary object that represents a simpler, cleaner version of this object for
        # generating collision. We carve holes in this simpler version for things like window and
        # door frames. The result is typically a concave object, and collision meshes need to be
        # convex; to fix that, we process it through a convex decomposition algorithm.
        collision_ob = create_blank_copy_of(src_ob)

        make_convex_hull(collision_ob)

        carve_openings_in_collision_mesh(
            collision_ob,
            openings=wall_openings_of(src_ob)
        )

        decompose_into_convex_parts(collision_ob)

        # Now, move all the convex parts of the collision object that are its children up to be its
        # sibling and then delete it, since we no longer need it.
        reparent_children_to_grandparent(collision_ob)
        delete_object(collision_ob)

        repaint_screen()

    print("")
    deselect_all_objects()


def carve_openings_in_collision_mesh(collision_ob, openings):
    deselect_all_objects()

    subtraction_objects = []
    multipart_openings = defaultdict(list)

    for opening in openings:
        multipart_match = multipart_opening_regex.match(opening.name)

        # Special case: Collect multi-part openings for now so we can join them together, later.
        if multipart_match is not None:
            prefix = multipart_match.group('Prefix')
            multipart_openings[prefix].append(opening)
            continue

        print(f"    - Preparing to carve opening of '{opening.name}'...")

        subtraction_ob = create_inplace_copy_of(opening)

        solidify_subtraction_ob(subtraction_ob)
        subtraction_objects.append(subtraction_ob)
        repaint_screen()

    # Special case: Multi-part openings need to be joined together before we use them.
    for prefix, openings in multipart_openings.items():
        print(f"    - Preparing to carve openings for '{prefix}'...")

        # Even more special case: An opening that looks like a multi-part opening, but actually is
        # just a single opening. In that case, handle it as if it were not multi-part. We couldn't
        # do this in the first loop above because we needed to identify all the openings that were
        # part of this list of openings first.
        if len(openings) == 1:
            subtraction_ob = create_inplace_copy_of(openings[0])
            solidify_subtraction_ob(subtraction_ob)
        else:
            multipart_subtraction_obs = []

            # Create duplicates of all the openings and then join them together.
            #
            # BUGBUG: We can't solidify the combined opening because it results in gaps between the
            # openings.
            for opening in openings:
                multipart_subtraction_ob = create_inplace_copy_of(opening)
                multipart_subtraction_obs.append(multipart_subtraction_ob)

            subtraction_ob = join_objects(multipart_subtraction_obs)

        subtraction_objects.append(subtraction_ob)

        repaint_screen()

    multipart_openings = None

    if len(subtraction_objects) > 0:
        print(f"    - Carving openings...")
        # Join the subtraction meshes into a single mesh, so we only have to carve the collision
        # mesh once. This reduces the number of artifacts we introduce into the collision mesh.
        subtraction_ob = join_objects(subtraction_objects)

        focus_on_object_in_viewport(collision_ob)

        # Clean up any remaining artifacts in the subtraction mesh. The resolution used for the
        # remesh impacts how closely the collision meshes follows the contour of each opening in the
        # collision mesh.
        remesh_high_resolution(subtraction_ob)
        repaint_screen()

        deselect_all_objects()
        subtraction_ob.select_set(True)
        collision_ob.select_set(True)
        bpy.context.view_layer.objects.active = collision_ob

        bpy.ops.object.modifier_apply(modifier="Auto Boolean")
        bpy.ops.object.boolean_auto_difference()
        repaint_screen()

        # Remesh the result, since boolean operations can ruin topology.
        remesh_medium_resolution(collision_ob)

    deselect_all_objects()
    repaint_screen()


def generate_roof_collision():
    print("")
    print("Generating collision for roofs...")

    roof_obs = [
        o for o in bpy.data.objects
        if o.type == 'MESH' and roof_collision_regex.match(o.name)
    ]

    for src_ob in roof_obs:
        print(f"  - Generating roof collision for '{src_ob.name}':")

        deselect_all_objects()

        focus_on_object_in_viewport(src_ob)
        repaint_screen()

        collision_ob = create_blank_copy_of(src_ob)

        print("    - Splitting collision mesh into convex pieces...")
        decompose_into_convex_parts(collision_ob)

        # Now, move all the convex parts of the collision object that are its children up to be its
        # sibling and then delete it, since we no longer need it.
        reparent_children_to_grandparent(collision_ob)
        delete_object(collision_ob)

        repaint_screen()

    print("")
    deselect_all_objects()


def generate_slab_collision():
    print("")
    print("Generating collision for slabs...")

    slab_obs = [
        o for o in bpy.data.objects
        if o.type == 'MESH' and slab_collision_regex.match(o.name)
    ]

    for src_ob in slab_obs:
        print(f"  - Generating slab collision for '{src_ob.name}':")

        deselect_all_objects()

        focus_on_object_in_viewport(src_ob)
        repaint_screen()

        collision_ob = create_blank_copy_of(src_ob)

        bpy.context.view_layer.objects.active = collision_ob

        ensure_object_mode()

        # Rebuild the slab with the Remesh modifier to eliminate artifacts/errors in the mesh from Live Home.
        print("    - Rebuilding collision mesh geometry...")
        remesh_very_high_resolution(collision_ob)
        repaint_screen()

        # Make collision mesh height match height of original mesh; it might end up being shorter.
        # The origin of each object must be set to its center for this to work properly; otherwise,
        # it's scaling relative to the world origin.
        translate_origin_to_midpoint(src_ob)
        translate_origin_to_midpoint(collision_ob)

        collision_ob.dimensions.z = src_ob.dimensions.z

        translate_origin_to_world_origin(src_ob)
        translate_origin_to_world_origin(collision_ob)

        carve_openings_in_collision_mesh(
            collision_ob,
            openings=floor_openings_that_intersect(collision_ob)
        )

        print("    - Splitting collision mesh into convex pieces...")
        decompose_into_convex_parts(collision_ob)

        # Now, move all the convex parts of the collision object that are its children up to be its
        # sibling and then delete it, since we no longer need it.
        reparent_children_to_grandparent(collision_ob)
        delete_object(collision_ob)

        repaint_screen()

    print("")
    deselect_all_objects()


def scale_object_from_center(ob, scale):
    ensure_object_mode()
    deselect_all_objects()

    ob.select_set(True)
    bpy.context.view_layer.objects.active = ob

    # Move origin to the center of the object, to scale relative to that point.
    bpy.ops.object.origin_set(type='ORIGIN_CENTER_OF_VOLUME', center='MEDIAN')

    # Actually scale it.
    bpy.ops.transform.resize(value=scale)
    bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)

    # Move origin to the center of the scene.
    bpy.context.scene.cursor.location = Vector((0.0, 0.0, 0.0))
    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')

    deselect_all_objects()


def create_blank_copy_of(src_ob):
    copy_ob = create_inplace_copy_of(src_ob)

    copy_ob.name = src_ob.name + "_blank"

    remove_all_materials(copy_ob)
    remove_all_uv_maps(copy_ob)

    return copy_ob


def create_inplace_copy_of(src_ob):
    copy_ob = src_ob.copy()

    copy_ob.data = src_ob.data.copy()
    copy_ob.show_wire = True
    copy_ob.parent = src_ob

    # Shift coordinate system of child, so it doesn't get offset by parent.
    copy_ob.matrix_parent_inverse = src_ob.matrix_world.inverted()

    if src_ob.users_collection:
        parent_collection = src_ob.users_collection[0]
        set_parent_collection(copy_ob, parent_collection.name)

    return copy_ob


def reparent_children_to_grandparent(parent_ob, update_naming_convention=True):
    grandparent_ob = parent_ob.parent

    for child_ob in parent_ob.children:
        child_ob.parent = grandparent_ob

        # Shift coordinate system of child, so it doesn't get offset by new parent.
        child_ob.matrix_parent_inverse = grandparent_ob.matrix_world.inverted()

        if update_naming_convention:
            print(f"Replacing '{parent_ob.name}' with '{grandparent_ob.name}' in '{child_ob.name}'...")
            # Adjust the naming convention of the child so that it's named after the grandparent
            # instead of the parent.
            child_ob.name = child_ob.name.replace(parent_ob.name, grandparent_ob.name)


def join_objects(objects):
    """
    Joins multiple objects into a single object, then returns the result.

    If an empty list of objects are passed in, None is returned.
    If a list containing only a single object is passed in, that object is returned.

    :param objects: The list of objects to join.
    :return: Either the joined object; or, None if no objects were provided.
    """
    if len(objects) == 0:
        return None

    if len(objects) == 1:
        return objects[0]

    for ob in objects:
        # Mark object for joining.
        ob.select_set(True)

        # Retain original object name by stashing it in a vertex group associated with the
        # appropriate vertices.
        bpy.context.view_layer.objects.active = ob
        bpy.ops.object.mode_set(mode='EDIT')
        bpy.ops.object.vertex_group_add()

        ob.vertex_groups[-1].name = ob.name

        bpy.ops.mesh.select_mode(use_extend=False, use_expand=False, type='VERT')
        bpy.ops.mesh.select_all(action='SELECT')
        bpy.ops.object.vertex_group_assign()

        bpy.ops.object.mode_set(mode='OBJECT')

    # Ensure we have a selection to avoid the warning, "Active object is not a selected mesh"
    bpy.context.view_layer.objects.active = objects[0]

    bpy.ops.object.join()

    # Capture the resulting joined object.
    joined_ob = bpy.context.view_layer.objects.active

    return joined_ob


def delete_object(ob):
    with bpy.context.temp_override(selected_objects=[ob], active_object=ob):
        bpy.ops.object.delete()


def wall_openings_of(parent_ob):
    ob_specific_regex_str = \
        wall_opening_regex_str.replace('$NAME$', parent_ob.name)

    ob_specific_regex = \
        re.compile(ob_specific_regex_str)

    for opening_ob in [o for o in bpy.data.objects if ob_specific_regex.match(o.name)]:
        yield opening_ob


def floor_openings_that_intersect(collision_ob):
    openings = [
        o for o in bpy.data.objects if
        floor_opening_regex.match(o.name) and do_meshes_overlap(collision_ob, o)
    ]

    for opening_ob in openings:
        yield opening_ob


def solidify_subtraction_ob(subtraction_ob):
    deselect_all_objects()

    subtraction_ob.select_set(True)
    bpy.context.view_layer.objects.active = subtraction_ob

    # Eliminate excess faces before making the convex hull.
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.dissolve_limited()
    bpy.ops.object.mode_set(mode='OBJECT')

    # Make a solid object out of the opening.
    make_convex_hull(subtraction_ob)
    repaint_screen()

    # Scale the subtraction object up by 15% so that it extends outside the collision object for
    # boolean subtraction to work properly.
    bpy.ops.object.mode_set(mode='OBJECT')
    bpy.ops.object.modifier_add(type='SOLIDIFY')
    bpy.context.object.modifiers["Solidify"].thickness = 0.15
    bpy.context.object.modifiers["Solidify"].offset = 0
    bpy.ops.object.modifier_apply(modifier="Solidify")
    repaint_screen()

    # Make the hollow center of the subtraction object solid.
    make_convex_hull(subtraction_ob)


def remesh_very_high_resolution(ob):
    remesh(ob, resolution_passes=10, scale=0.990)


def remesh_high_resolution(ob):
    remesh(ob, resolution_passes=8, scale=0.990)


def remesh_medium_resolution(ob):
    remesh(ob, resolution_passes=8, scale=0.900)


def remesh_low_resolution(ob):
    remesh(ob, resolution_passes=4, scale=0.900)


def remesh(ob, resolution_passes, scale):
    deselect_all_objects()
    ob.select_set(True)
    bpy.context.view_layer.objects.active = ob

    bpy.ops.object.modifier_add(type='REMESH')
    bpy.context.object.modifiers["Remesh"].mode = 'BLOCKS'
    bpy.context.object.modifiers["Remesh"].octree_depth = resolution_passes
    bpy.context.object.modifiers["Remesh"].scale = scale
    bpy.context.object.modifiers["Remesh"].threshold = 0.5
    bpy.ops.object.modifier_apply(modifier="Remesh")

    deselect_all_objects()


def make_all_faces_convex(ob):
    ob.select_set(True)
    bpy.context.view_layer.objects.active = ob
    bpy.ops.object.mode_set(mode='EDIT')

    # This is what actually defines the new geometry -- Blender creates the
    # convex shapes we need to split by.
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.vert_connect_concave()
    bpy.ops.mesh.select_all(action='DESELECT')


def get_bvh_tree(obj):
    """Create a BVH tree for a given object."""
    mesh = obj.data

    bm = bmesh.new()
    bm.from_mesh(mesh)
    bm.transform(obj.matrix_world)

    bvh = BVHTree.FromBMesh(bm)

    bm.free()

    return bvh


def do_meshes_overlap(obj1, obj2):
    """Check if two objects' meshes overlap using BVH trees."""
    bvh1 = get_bvh_tree(obj1)
    bvh2 = get_bvh_tree(obj2)

    # Check for intersections
    return bvh1.overlap(bvh2)


def make_convex_hull(ob):
    deselect_all_objects()
    ensure_object_mode()

    ob.select_set(True)
    bpy.context.view_layer.objects.active = ob

    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_mode(use_extend=False, use_expand=False, type='VERT')
    bpy.ops.mesh.select_all(action='SELECT')

    bpy.ops.mesh.convex_hull(
        delete_unused=True,
        use_existing_faces=False,
        join_triangles=True)

    mesh = ob.data
    bm = bmesh.from_edit_mesh(mesh)

    # Clean-up unnecessary edges.
    bmesh.ops.dissolve_limit(
        bm,
        angle_limit=radians(5),
        verts=bm.verts,
        edges=bm.edges,
    )

    bm.free()

    ensure_object_mode()
    deselect_all_objects()


def deselect_all_objects():
    ensure_object_mode()
    bpy.ops.object.select_all(action='DESELECT')


def clear_file():
    # Clear all objects from the scene
    ensure_object_mode()
    bpy.ops.object.select_all(action='SELECT')
    bpy.ops.object.delete()

    # Clear all collections from the scene
    for collection in bpy.data.collections:
        bpy.data.collections.remove(collection)

    bpy.ops.outliner.orphans_purge()


def remove_collection_by_name_if_empty(collection_name):
    if (collection_name in bpy.data.collections and
            len(bpy.data.collections[collection_name].children) == 0):
        remove_collection_by_name(collection_name)


def remove_collection_by_name(collection_name):
    collections = bpy.data.collections
    collections.remove(collections[collection_name])


def create_collection_if_not_exist(collection_name):
    if collection_name not in bpy.data.collections:
        print("Creating collection: " + collection_name)
        bpy.data.collections.new(collection_name)
        bpy.context.scene.collection.children.link(bpy.data.collections[collection_name])


def remove_from_all_collections(ob):
    for collection in ob.users_collection:
        remove_from_collection(ob, collection)


def remove_from_collection(ob, collection):
    if ob.name in collection.objects:
        collection.objects.unlink(ob)


def set_parent_collection(ob, collection_name):
    remove_from_all_collections(ob)
    create_collection_if_not_exist(collection_name)
    bpy.data.collections[collection_name].objects.link(ob)


def remove_all_materials(ob):
    with bpy.context.temp_override(active_object=ob):
        ob.select_set(True)
        bpy.context.view_layer.objects.active = ob

        for i in range(len(ob.material_slots)):
            ob.active_material_index = i
            bpy.ops.object.material_slot_remove()


def remove_all_uv_maps(ob):
    with bpy.context.temp_override(active_object=ob):
        ob.select_set(True)
        bpy.context.view_layer.objects.active = ob

        uv_layers = ob.data.uv_layers
        uv_layers_to_remove = uv_layers[:]

        while uv_layers_to_remove:
            uv_layers.remove(uv_layers_to_remove.pop())


def ensure_object_mode():
    if bpy.context.active_object is not None and bpy.context.active_object.mode != 'OBJECT':
        bpy.ops.object.mode_set(mode='OBJECT')


def focus_on_object_in_viewport(ob):
    # Find the 3D view area.
    area3d = next((area for area in bpy.context.screen.areas if area.type == "VIEW_3D"), None)

    if area3d:
        # Find the 3D region within the 3D view area.
        region3d = next((region for region in area3d.regions if region.type == "WINDOW"), None)

        if region3d:
            # Override context for both area and region.
            with bpy.context.temp_override(area=area3d,
                                           region=region3d):
                space3d = area3d.spaces.active

                # Toggle out of local view.
                if space3d.local_view:
                    bpy.ops.view3d.localview()

                ob.select_set(True)

                # Toggle into local view.
                bpy.ops.view3d.localview()
                bpy.ops.view3d.view_selected()
                ob.select_set(False)


def center_scene_in_viewport():
    # Find the 3D view area.
    area3d = next((area for area in bpy.context.screen.areas if area.type == "VIEW_3D"), None)

    if area3d:
        # Find the 3D region within the 3D view area.
        region3d = next((region for region in area3d.regions if region.type == "WINDOW"), None)

        if region3d:
            # Override context for both area and region.
            with bpy.context.temp_override(area=area3d,
                                           region=region3d):
                space3d = area3d.spaces.active

                # Toggle out of local view.
                if space3d.local_view:
                    bpy.ops.view3d.localview()

                bpy.ops.view3d.view_all(use_all_regions=True)

                for i in range(3):
                    bpy.ops.view3d.zoom(delta=1)

    repaint_screen()


def repaint_screen_and_pause(pause_sec=5):
    """
    Repaints the screen and then pauses for the specified amount of time, to give the user a
    preview of what's happening.

    :param pause_sec: An optional amount of time to pause. Defaults to 5 seconds.
    """
    import time

    repaint_screen()
    time.sleep(pause_sec)


def repaint_screen():
    bpy.context.view_layer.update()
    bpy.ops.wm.redraw_timer(type='DRAW_WIN_SWAP', iterations=1)


def status_print(msg):
    formatted_msg = "%-120s" % msg
    sys.stdout.write(formatted_msg + (chr(8) * len(formatted_msg)))
    sys.stdout.flush()


def decompose_into_convex_parts(ob):
    """
    Decompose an object into convex parts using the "Convex Decomposition" add-on.

    :param ob: The input object to decompose.
    """
    ob.select_set(True)
    bpy.context.view_layer.objects.active = ob

    bpy.context.scene.ConvDecompProperties.transparency = 50
    bpy.context.scene.ConvDecompProperties.hull_collection_name = ""
    bpy.context.scene.ConvDecompProperties.solver = 'CoACD'
    bpy.context.scene.ConvDecompPropertiesCoACD.f_threshold = 0.025
    bpy.ops.opr.convex_decomposition_run()


clear_file()

import_fbx(fbx_path)
center_scene_in_viewport()

cleanup_scene()
center_scene_in_viewport()

shade_all_objects_flat()
setup_uvs()
assign_unique_materials_by_face_normals()

generate_collision()
center_scene_in_viewport()

export_all_collections_to_fbx()

print("Done!")
