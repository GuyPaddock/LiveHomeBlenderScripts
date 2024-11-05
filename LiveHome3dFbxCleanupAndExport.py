##
# This script can be run in Blender to re-arrange and clean-up an FBX model from
# Live Home 3D Pro so that it's more suitable for use in Unreal Engine 4/5.
#
# All objects in Live Home 3D should follow a naming convention similar to UE4
# naming conventions:
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
#   SM_House_Roof_Main_Gable_01
#   SM_House_Roof_Main_Side_01
#   SM_House_Roof_Main_Side_02
#
# Live Home 3D adds a variable-length, random string of characters to the end of
# every object during export. So, the raw export from Live Home 3D will contain
# objects with names like the following (and the random string changes during
# each export):
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
#   SM_House_Roof_Main_Gable_01_3pBdtTXyfB0OJ19mch3Bj3
#   SM_House_Roof_Main_Side_01_0ej0KfnaD95PJR96NuIZFJ
#   SM_House_Roof_Main_Side_02_3CiZR4Rqj8z9PvTm60swBL
#
# This script will strip off those random characters and organize all the
# pieces of the house into collections by room and element. For example, the
# following collections would be created from the objects listed in the example
# above:
#   - SM_BackPorch_Ceiling
#   - SM_BackPorch_Floor
#   - SM_BackPorch_Wall_01
#   - SM_BackStairwell_Roof
#   - SM_House_Roof_Main
#
# This script will perform the following steps:
#   1. Remove all objects that are not meshes (including parent objects).
#   2. Fix-up the naming of "Slab" objects that Live Home 3D generates itself,
#      since these objects cannot be renamed inside Live Home 3D itself.
#   3. Organize objects into collections by room and element.
#   4. Adjusts the position of the house model so that its center on the X and
#      Y axes matches the origin of the world.
#   5. Converts triangles to quads and eliminates split normals (in case there
#      are any; generally this doesn't seem to be the case with LH3D exports).
#   6. Generates a secondary UV map for UE4 lighting, so that UE does not
#      encounter overlapping UVs during lightmap generation.
#   7. Re-generates the primary UV map using cube projection so that the UVs are
#      more reasonable and applying materials to walls in UE doesn't end up
#      looking like a ransom note or hodgepodge of text pieces.
#   8. (Optionally) Applies Blender's UV checkboard test pattern texture to all
#      meshes so that it's easy to spot problems with the mesh UVs while in
#      Blender.
#   9. Generates basic convex hull collision for all posts, walls, and stairs.
#  10. Generates complex collision for slabs (ceilings/floors) using remesh and
#      a convex hull decomposition algorithm.
#  11. Exports each collection of meshes as separate FBX files in the same
#      folder where the Blender project file has been saved.
#
# Dependencies:
#   - Blender 4.0.
#   - Object: Bool Tool plug-in enabled.
#
# @author Guy Elsmore-Paddock <guy.paddock@gmail.com>
# @author Aaron Powell <aaron@lunadigital.tv>
#

import bmesh
import bpy
import math
import operator
import re
import sys
import time

from collections import OrderedDict
from itertools import combinations, count
from math import atan2, pi, radians, degrees
from mathutils import Vector
from pathlib import Path

fbx_path = r"C:\PATH\TO\SWEET_HOME\Export.fbx"

element_regex_str = \
    r"^SM_(?P<Room>(?:[^_]+))_(?P<Element>(?:(?:(?:Conduit(?:_\d{2})?_)?" \
    r"(?:Closet_)?)(?:CeilingTrim" \
    r"|Ceiling" \
    r"|Floor(?:_\d{2}(?:_Slab)?)?" \
    r"|(?:Stair)?Wall_\d{2}(?:_(?:(?:Moulding_(?:Base|Crown)_(?:Left|Right))" \
    r"|(?:Garden)?Window(?:_\d{2})?(?:_Opening)?" \
    r"|Door_\d{2}(?:_Opening)?" \
    r"|Opening(?:_\d{2})?))?" \
    r"|WallPanel(?:_\d{2})?|Roof((?:_\d{2})|_Main)?" \
    r"(?:_(?:Gable|Hole|Side|SegmentedSide|Vent)(?:_\d{2})?)?" \
    r"(?:_Window_\d{2}(?:_Opening)?)?" \
    r"|Post(?:_\d{2})?" \
    r"|Stairs(?:_Opening)?" \
    r"|Conduit" \
    r"|Tub_Shelf)))?(?P<Garbage>.*)$"

prefix_regex_str = \
    r"^(?P<Prefix>(?:Closet_)?(?:Conduit(?:_\d{2})?_)?" \
    r"(?:CeilingTrim|Ceiling|Floor|Post|Roof|Slab|StairWall|Stairs|Tub_Shelf" \
    r"|WallPanel|Wall)(?:_\d{2})?)"

basic_collision_regex_str = r"^.+_(?:(?:Wall|Post|StairWall|.*PorchCeiling)(?:_\d{2})?)$"
slab_collision_regex_str = r"^House_Floor_\d{2}_Slab$"

wall_opening_regex_str = r"^$NAME$_(?:(Door|Window)_[0-9]{2}_)?Opening(?:_[0-9]{2})?$"
floor_opening_regex_str = r"^.+_Stairs_Opening$"

element_regex = re.compile(element_regex_str)
prefix_regex = re.compile(prefix_regex_str)

basic_collision_regex = re.compile(basic_collision_regex_str)
slab_collision_regex = re.compile(slab_collision_regex_str)

floor_opening_regex = re.compile(floor_opening_regex_str)


def import_fbx(path):
    bpy.ops.import_scene.fbx(filepath=path)


def cleanup_scene():
    print("")
    print("=== Cleaning up the scene ===")

    remove_unwanted_objects()
    assign_slab_names()
    group_objects_by_room_and_type()
    translate_origin_of_all_objects_to_world_origin()
    simplify_geometry()


def setup_uvs():
    # NOTE: If Blender crashes when running this, make sure you are running
    # Blender 2.91.2 or later; it fixes https://developer.blender.org/T85253.
    generate_lightmap_uvs()
    generate_diffuse_uvs()


def generate_collision():
    print("")
    print("=== Generating collision ===")

    generate_basic_collision()
    generate_slab_collision()


def export_all_collections_to_fbx():
    print("")
    print("=== Exporting scene to FBX ===")

    for coll in bpy.data.collections:
        status_print("  - Exporting collection '" + coll.name + "' to FBX...")

        try:
            bpy.ops.export_scene.fbx(
                {
                    'object': None,
                    'active_object': None,
                    'selected_objects': coll.all_objects
                },
                filepath=str(
                    Path(bpy.data.filepath).parent / f"{coll.name}.fbx"
                ),
                use_selection=True,
                mesh_smooth_type='FACE',
                use_tspace=True,
                bake_space_transform=True,
            )

        except RuntimeError:
            print("FBX export error:", sys.exc_info()[0])

            # Pause to catch user's attention
            time.sleep(2)

    print("")


def remove_unwanted_objects():
    print("Removing unwanted, non-mesh objects...")

    meshes = [o for o in bpy.data.objects if o.type == 'MESH']
    non_meshes = [o for o in bpy.data.objects if o.type != 'MESH']

    for ob in meshes:
        print("  - Keeping '" + ob.name + "' (type '" + ob.type + "').")

    for ob in non_meshes:
        print("  - Deleting '" + ob.name + "' (type '" + ob.type + "').")

    # Remove the link between the meshes and their parents before we remove the
    # unwanted parent objects.
    with bpy.context.temp_override(selected_objects=meshes):
        bpy.ops.object.parent_clear(type='CLEAR_KEEP_TRANSFORM')

    with bpy.context.temp_override(selected_objects=non_meshes):
        bpy.ops.object.delete()


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
                        print(
                            f"  - Creating collection prefix '{element_prefix}'."
                        )
                        prefixes.append(element_prefix)

            if garbage is not None:
                ob.name = ob.name.replace(garbage, '')

    for ob in [o for o in bpy.data.objects if o.type == 'MESH']:
        for prefix in prefixes:
            if ob.name.startswith(prefix):
                print(
                    f"  - Adding '{ob.name}' to collection prefix '{prefix}'."
                )

                # Remove static mesh prefix since it moved up to the collection
                # and filename.
                ob.name = ob.name.replace('SM_', '')

                set_parent_collection(ob, prefix)


def translate_origin_to_midpoint(ob):
    ob.select_set(True)
    bpy.ops.object.origin_set(type='ORIGIN_GEOMETRY', center='BOUNDS')


def translate_origin_to_world_origin(ob):
    bpy.context.view_layer.objects.active = ob
    ob.select_set(True)

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

    cursor = bpy.context.scene.cursor
    cursor.location = sum([o.matrix_world.translation for o in obs], Vector()) / n
    cursor.location.z = 0

    # Move objects back to origin of scene
    for ob in bpy.data.objects:
        if bpy.data.objects.get(ob.name):
            status_print("  - Adjusting origin of '" + ob.name + "'...")

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

    # This doesn't properly snap instances but that might be ok for now
    cursor.location = (0, 0, 0)

    for ob in bpy.data.objects:
        bpy.context.view_layer.objects.active = ob
        bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')


def simplify_geometry():
    print("Simplifying model geometry...")

    for ob in [o for o in bpy.data.objects if o.type == 'MESH']:
        status_print("  - Simplifying '" + ob.name + "'...")

        deselect_all_objects()

        bpy.context.view_layer.objects.active = ob

        bpy.ops.object.mode_set(mode='EDIT')
        bpy.ops.mesh.select_all(action='SELECT')

        bpy.ops.mesh.tris_convert_to_quads()
        bpy.ops.mesh.remove_doubles()
        bpy.ops.mesh.customdata_custom_splitnormals_clear()

    print("")
    deselect_all_objects()


def generate_diffuse_uvs():
    print("Cube-projecting new UVs on each mesh...")

    uv_map_name = 'DiffuseUV'

    # deselect all to make sure select one at a time
    deselect_all_objects()

    apply_uv_func(uv_map_name, box_uv_project)


def generate_lightmap_uvs():
    print("Generating secondary UV for UE4 lightmaps on each mesh...")

    uv_map_name = 'Lightmap'

    # deselect all to make sure select one at a time
    deselect_all_objects()

    apply_uv_func(uv_map_name, smart_uv_project)


def box_uv_project():
    bpy.ops.uv.cube_project(cube_size=0.5)


def smart_uv_project():
    bpy.ops.uv.smart_project(angle_limit=66, island_margin=0.02)


def apply_uv_func(uv_map_name, func):
    for ob in [o for o in bpy.data.objects if o.type == 'MESH']:
        status_print(f"  - Projecting {uv_map_name} for '{ob.name}'...")

        # From https://blender.stackexchange.com/a/120807
        bpy.context.view_layer.objects.active = ob
        ob.select_set(True)

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


def apply_uv_grid():
    print("Applying UV grid test pattern to each mesh...")

    image_name = "UV Grid"

    # Call the operator
    bpy.ops.image.new(
        name=image_name,
        width=1024,
        height=1024,
        color=(0.0, 0.0, 0.0, 1.0),
        alpha=True,
        generated_type='UV_GRID',  # BLANK, COLOR_GRID
        float=False,
        use_stereo_3d=False,
        tiled=False
    )

    image = bpy.data.images.get(image_name)

    if image:
        mat = bpy.data.materials.new(name="UV Grid")
        mat.use_nodes = True
        bsdf = mat.node_tree.nodes["Principled BSDF"]

        tex_image = mat.node_tree.nodes.new('ShaderNodeTexImage')
        tex_image.image = image

        mat.node_tree.links.new(
            bsdf.inputs['Base Color'],
            tex_image.outputs['Color']
        )

        for ob in [o for o in bpy.data.objects if o.type == 'MESH']:
            status_print("  - Applying UV grid to '" + ob.name + "'...")

            if len(ob.data.materials) != 0:
                ob.data.materials[0] = mat
            else:
                ob.data.materials.append(mat)

            deselect_all_objects()
            ob.select_set(True)
            bpy.context.view_layer.objects.active = ob

            bpy.ops.object.mode_set(mode='EDIT')
            bpy.context.tool_settings.mesh_select_mode = [False, False, True]
            bpy.ops.mesh.select_all(action='SELECT')

            ob.active_material_index = 0
            bpy.ops.object.material_slot_assign()

        print("")


def generate_basic_collision():
    print("")
    print("Generating collision for simple objects...")

    collision_obs = [
        o for o in bpy.data.objects
        if o.type == 'MESH' and basic_collision_regex.match(o.name)
    ]

    for src_ob in collision_obs:
        status_print("  - Generating collision for '" + src_ob.name + "'...")

        deselect_all_objects()

        collision_ob = create_collision_mesh_from(src_ob)

        make_convex_hull(collision_ob)

        carve_openings_in_collision_mesh(
            collision_ob,
            openings=wall_openings_of(src_ob)
        )

        split_into_convex_pieces(
            collision_ob,
            create_closed_objects=False,
            matchup_degenerates=False
        )

        # Uncomment this line if you don't want collision meshes to have any
        # faces so that the model looks "neater" in Blender. It has no impact on
        # collision calculation in UE4, but removing the faces makes it harder
        # to customize the collision mesh before export.
        # bpy.ops.mesh.delete(type="ONLY_FACE")

    print("")
    deselect_all_objects()


def carve_openings_in_collision_mesh(collision_ob, openings):
    deselect_all_objects()

    for opening in openings:
        subtraction_mesh = create_inplace_copy_of(opening)

        # Make a solid object out of the opening.
        make_convex_hull(subtraction_mesh)

        bpy.context.view_layer.objects.active = subtraction_mesh
        subtraction_mesh.select_set(True)

        bpy.ops.object.mode_set(mode='OBJECT')
        bpy.ops.object.modifier_add(type='SOLIDIFY')
        bpy.context.object.modifiers["Solidify"].thickness = 0.1
        bpy.context.object.modifiers["Solidify"].offset = 0

        bpy.ops.object.modifier_apply(modifier="Solidify")

        # Make the hollow center of the object solid.
        make_convex_hull(subtraction_mesh)

        deselect_all_objects()

        bpy.context.view_layer.objects.active = collision_ob

        subtraction_mesh.select_set(True)
        collision_ob.select_set(True)

        bpy.ops.object.modifier_apply(modifier="Auto Boolean")
        bpy.ops.object.boolean_auto_difference()

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

        collision_ob = create_collision_mesh_from(src_ob)

        bpy.context.view_layer.objects.active = collision_ob
        bpy.ops.object.mode_set(mode='OBJECT')

        print("    - Filling in open faces (top and bottom) of collision mesh...")
        bpy.ops.object.mode_set(mode='EDIT')
        bpy.ops.mesh.decimate(ratio=0.4, vertex_group_factor=1)
        bpy.context.tool_settings.mesh_select_mode = [True, False, False]
        bpy.ops.mesh.select_all(action='SELECT')

        try:
            # One or both of these can fail depending on the geometry.
            print("    - Filling in collision mesh (pass 1 of 2)...")
            bpy.ops.mesh.edge_face_add()

            print("    - Filling in collision mesh (pass 2 of 2); this may fail without penalty...")
            bpy.ops.mesh.edge_face_add()
        except:
            pass

        bpy.ops.object.mode_set(mode='OBJECT')

        print("    - Rebuilding collision mesh geometry (pass 1 of 2)...")
        # Rebuild the slab with the Remesh modifier to eliminate
        # artifacts/errors in the mesh from Live Home
        bpy.ops.object.modifier_add(type='REMESH')
        bpy.context.object.modifiers["Remesh"].mode = 'SHARP'
        bpy.context.object.modifiers["Remesh"].octree_depth = 8
        bpy.context.object.modifiers["Remesh"].scale = 0.785
        bpy.context.object.modifiers["Remesh"].sharpness = 1
        bpy.context.object.modifiers["Remesh"].threshold = 1
        bpy.context.object.modifiers["Remesh"].use_smooth_shade = True
        bpy.ops.object.modifier_apply(modifier="Remesh")

        print("    - Rebuilding collision mesh geometry (pass 2 of 2)...")
        # Use a second Remesh pass to eliminate artifacts introduced or
        # exacerbated by the prior pass.
        bpy.ops.object.modifier_add(type='REMESH')
        bpy.context.object.modifiers["Remesh"].mode = 'SHARP'
        bpy.context.object.modifiers["Remesh"].octree_depth = 8
        bpy.context.object.modifiers["Remesh"].scale = 0.990
        bpy.context.object.modifiers["Remesh"].sharpness = 1
        bpy.context.object.modifiers["Remesh"].threshold = 1
        bpy.context.object.modifiers["Remesh"].use_smooth_shade = True
        bpy.ops.object.modifier_apply(modifier="Remesh")

        print("    - Simplifying faces of collision mesh geometry...")
        # Simplify the slab collision; this typically can reduce the mesh from
        # more than 70,000 faces to fewer than 64 faces.
        bpy.ops.object.modifier_add(type='DECIMATE')
        bpy.context.object.modifiers["Decimate"].decimate_type = 'DISSOLVE'
        bpy.ops.object.modifier_apply(modifier="Decimate")

        # Make collision mesh height match height of original mesh; it might
        # end up being shorter. The origin of each object must be set to its center
        # for this to work properly; otherwise, it's scaling relative to the world
        # origin.
        translate_origin_to_midpoint(src_ob)
        translate_origin_to_midpoint(collision_ob)

        collision_ob.dimensions.z = src_ob.dimensions.z

        translate_origin_to_world_origin(src_ob)
        translate_origin_to_world_origin(collision_ob)

        carve_openings_in_collision_mesh(
            collision_ob,
            openings=floor_openings()
        )

        print("    - Splitting collision mesh into convex pieces...")
        split_into_convex_pieces(
            collision_ob,
            create_closed_objects=False,
            matchup_degenerates=False
        )

        # Uncomment this line if you don't want collision meshes to have any
        # faces so that the model looks "neater" in Blender. It has no impact on
        # collision calculation in UE4, but removing the faces makes it harder
        # to customize the collision mesh before export.
        # bpy.ops.mesh.delete(type="ONLY_FACE")

    print("")
    deselect_all_objects()


def create_collision_mesh_from(src_ob):
    collision_ob = create_inplace_copy_of(src_ob)

    collision_ob.name = 'UCX_' + src_ob.name + "_01"

    remove_all_materials(collision_ob)
    remove_all_uv_maps(collision_ob)

    return collision_ob


def create_inplace_copy_of(src_ob):
    copy_ob = src_ob.copy()

    copy_ob.data = src_ob.data.copy()
    copy_ob.show_wire = True
    copy_ob.parent = src_ob

    # Shift coordinate system of child, so it doesn't get offset by parent
    copy_ob.matrix_parent_inverse = src_ob.matrix_world.inverted()

    if src_ob.users_collection:
        parent_collection = src_ob.users_collection[0]
        set_parent_collection(copy_ob, parent_collection.name)

    return copy_ob


def wall_openings_of(parent_ob):
    ob_specific_regex_str = \
        wall_opening_regex_str.replace('$NAME$', parent_ob.name)

    ob_specific_regex = \
        re.compile(ob_specific_regex_str)

    for opening_ob in [o for o in bpy.data.objects if ob_specific_regex.match(o.name)]:
        yield opening_ob


def floor_openings():
    for opening_ob in [o for o in bpy.data.objects if floor_opening_regex.match(o.name)]:
        yield opening_ob


def split_into_convex_pieces(ob, create_closed_objects=True,
                             matchup_degenerates=True):
    object_name = ob.name

    deselect_all_objects()
    make_all_faces_convex(ob)

    eliminated_piece_names = \
        split_on_convex_boundaries(
            ob,
            create_closed_objects,
            matchup_degenerates
        )

    rename_pieces(object_name, eliminated_piece_names)

    # Deselect everything, for the convenience of the user.
    deselect_all_objects()


def make_all_faces_convex(ob):
    bpy.context.view_layer.objects.active = ob
    bpy.ops.object.mode_set(mode='EDIT')

    # This is what actually defines the new geometry -- Blender creates the
    # convex shapes we need to split by.
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.vert_connect_concave()
    bpy.ops.mesh.select_all(action='DESELECT')


##
# Splits an object into smaller pieces by its convex, planar edges.
#
# In an ideal world, we could just split the object by all the edges that are
# attached to -- and are co-planar with -- the faces of the object, since those
# edges are most likely to represent the convex boundaries of the object. But,
# Blender does not provide an easy way to find such edges.
#
# Instead, we use several heuristics to simulate this type of selection:
#   1. First, we select all the sharp edges of the object, since sharp edges are
#      only co-planar with one of the faces they connect with and are therefore
#      unlikely to represent convex boundary edges.
#   2. Second, we select all edges that are similar in angle to the sharp edges,
#      to catch any edges that are almost steep enough to be sharp edges.
#   3. Third, we invert the selection, which should (hopefully) cause all the
#      convex boundary edges we want to be selected.
#   4. Fourth, we seek out any sharp edges that connect with the convex boundary
#      edges, since we will need to split on these edges as well so that our
#      "cuts" go all the way around the object (e.g. if the convex boundary
#      edges lay on the top and bottom faces of an object, we need to select
#      sharp edges to connect the top and bottom edges on the left and right
#      sides so that each split piece is a complete shape instead of just
#      disconnected, detached planes).
#   4. Next, we split the object by all selected edges, which should result in
#      creation of each convex piece we seek.
#
def split_on_convex_boundaries(ob, create_closed_objects=True,
                               matchup_degenerates=True):
    bpy.ops.object.mode_set(mode='EDIT')

    select_convex_boundary_edges(ob)

    # Now perform an vertex + edge split along each selected edge, which should
    # result in the object being broken-up along each planar edge and connected
    # sharp edges (e.g. on corners).
    bpy.ops.mesh.edge_split(type='VERT')

    # Now, just break each loose part off into a separate object.
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.separate(type='LOOSE')

    if create_closed_objects:
        # And then make each piece fully enclosed.
        return create_closed_shapes_from_pieces(ob, matchup_degenerates)
    else:
        return []


##
# Selects all edges that denote the boundaries of convex pieces.
#
# This is a multistep process driven by heuristics:
#   1. First, we select all the sharp edges of the object, since sharp edges are
#      only co-planar with one of the faces they connect with and are therefore
#      unlikely to represent convex boundary edges.
#   2. Second, we select all edges that are similar in length to the sharp
#      edges, to catch any edges that are almost steep enough to be sharp edges.
#   3. Third, we invert the selection, which should (hopefully) cause all the
#      convex boundary edges we want to be selected.
#
def select_convex_boundary_edges(ob, max_edge_length_proportion=0.1):
    bpy.ops.object.mode_set(mode='EDIT')

    mesh = ob.data
    bm = bmesh.from_edit_mesh(mesh)

    # Enter "Edge" select mode
    bpy.context.tool_settings.mesh_select_mode = [False, True, False]

    # Find all sharp edges and edges of similar length
    bpy.ops.mesh.select_all(action='DESELECT')
    bpy.ops.mesh.edges_select_sharp()
    bpy.ops.mesh.select_similar(type='EDGE_LENGTH', threshold=0.01)

    # Invert the selection to find the convex boundary edges.
    bpy.ops.mesh.select_all(action='INVERT')

    bm.faces.ensure_lookup_table()
    bm.edges.ensure_lookup_table()

    edges_to_select = []
    max_edge_length = max(ob.dimensions) * max_edge_length_proportion

    for selected_edge in [e for e in bm.edges if e.select]:
        edge_bridges = \
            find_shortest_edge_bridges(
                selected_edge,
                max_edge_length=max_edge_length
            )

        for path in edge_bridges.values():
            for edge in path:
                edges_to_select.append(edge)

    # Select the edges after we pick which edges we *want* to select, to ensure
    # that we only base our decisions on the initial convex boundary edges.
    for edge in edges_to_select:
        edge.select = True


##
# Locate the shortest path of edges to connect already-selected edges.
#
# This is used to find the additional edges that must be selected for a cut
# along a convex boundary to create a complete, closed object shape.
#
# The max edge length argument can be provided to avoid trying to find
# connections between convex boundaries that are very far apart in the same
# object.
#
def find_shortest_edge_bridges(starting_edge, max_edge_length=None):
    edge_bridges = find_bridge_edges(starting_edge, max_edge_length)
    sorted_edge_bridges = sorted(edge_bridges, key=lambda eb: eb[0])
    edge_solutions = {}

    for edge_bridge in sorted_edge_bridges:
        path_distance, final_edge, path = edge_bridge

        # Skip edges we've already found a min-length path to
        if final_edge not in edge_solutions.keys():
            edge_solutions[final_edge] = path

    print(f"Shortest edge bridges for starting edge '{str(starting_edge.index)}':")

    if len(edge_solutions) > 0:
        print(
            "  - " +
            "\n  - ".join(map(
                lambda i: str(
                    (i[0].index, str(list(map(lambda e: e.index, i[1]))))
                ),
                edge_solutions.items()
            )))
    print("")
    print("")

    return edge_solutions


##
# Performs a recursive, depth-first search from a selected edge to other edges.
#
# This returns all possible paths -- and distances of those paths -- to traverse
# the mesh from the starting, selected edge to another selected edge. To avoid
# a lengthy search, the max_depth parameter controls how many levels of edges
# are searched.
#
# The result is an array of tuples, where each tuple contains the total distance
# of the path, the already-selected edge that the path was able to reach, and
# the list of edges that would need to be selected in order to reach that
# destination edge.
#
def find_bridge_edges(edge, max_edge_length=None, max_depth=3, current_depth=0,
                      path_distance=0, edge_path=None, seen_verts=None):
    if edge_path is None:
        edge_path = []

    if seen_verts is None:
        seen_verts = []

    # Don't bother searching edges we've seen
    if edge in edge_path:
        return []

    if (current_depth > 0):
        first_edge = edge_path[0]
        edge_length = edge.calc_length()

        # Don't bother searching edges along the same normal as the first edge.
        # We want our cuts to be along convex boundaries that are perpendicular.
        if have_common_face(first_edge, edge):
            return []

        if edge.select:
            return [(path_distance, edge, edge_path)]

        # Disqualify edges that are too long.
        if max_edge_length is not None and edge_length > max_edge_length:
            print(
                f"Disqualifying edge {edge.index} because length [{edge_length}] > [{max_edge_length}"
            )

            return []

    if current_depth == max_depth:
        return []

    new_edge_path = edge_path + [edge]
    bridges = []

    for edge_vert in edge.verts:
        # Don't bother searching vertices we've already seen (no backtracking).
        if edge_vert in seen_verts:
            continue

        new_seen_verts = seen_verts + [edge_vert]

        for linked_edge in edge_vert.link_edges:
            # Don't bother searching selected edges connected to the starting
            # edge, since that gets us nowhere.
            if linked_edge.select and current_depth == 0:
                continue

            edge_length = linked_edge.calc_length()

            found_bridge_edges = find_bridge_edges(
                edge=linked_edge,
                max_edge_length=max_edge_length,
                max_depth=max_depth,
                current_depth=current_depth + 1,
                path_distance=path_distance + edge_length,
                edge_path=new_edge_path,
                seen_verts=new_seen_verts
            )

            bridges.extend(found_bridge_edges)

    return bridges


def create_closed_shapes_from_pieces(ob, matchup_degenerates=True,
                                     min_volume=0.1):
    print("Converting each piece into a closed object...")

    degenerate_piece_names = []

    for piece in name_duplicates_of(ob):
        if not make_piece_convex(piece):
            degenerate_piece_names.append(piece.name)

    degenerate_count = len(degenerate_piece_names)

    print("")
    print(f"Total degenerate (flat) pieces: {degenerate_count}")
    print("")

    eliminated_piece_names = []

    if matchup_degenerates:
        if degenerate_count > 10:
            # TODO: Hopefully, some day, find a good deterministic way to
            # automatically match up any number of degenerate pieces using a
            # heuristic that generates sane geometry.
            print(
                "There are too many degenerates for reliable auto-matching, so "
                "it will not be performed. You will need to manually combine "
                "degenerate pieces.")
            print("")
        else:
            eliminated_piece_names.extend(
                matchup_degenerate_pieces(degenerate_piece_names, min_volume)
            )

            eliminated_piece_names.extend(
                eliminate_tiny_pieces(degenerate_piece_names, min_volume)
            )

    return eliminated_piece_names


def matchup_degenerate_pieces(degenerate_piece_names, min_volume=0.1):
    pieces_eliminated = []
    degenerate_volumes = find_degenerate_combos(degenerate_piece_names)

    print("Searching for a way to match-up degenerates into volumes...")

    for piece1_name, piece1_volumes in degenerate_volumes.items():
        # Skip pieces already joined with degenerate pieces we've processed
        if piece1_name not in degenerate_piece_names:
            continue

        piece1 = bpy.data.objects[piece1_name]

        piece1_volumes_asc = dict(
            sorted(
                piece1_volumes.items(),
                key=operator.itemgetter(1)
            )
        )

        piece2 = None

        for piece2_name, combo_volume in piece1_volumes_asc.items():
            # Skip pieces that would make a volume that's too small, or that
            # have been joined with degenerate pieces we've processed
            if combo_volume < min_volume or piece2_name not in degenerate_piece_names:
                continue
            else:
                piece2 = bpy.data.objects[piece2_name]
                break

        if piece2 is not None:
            degenerate_piece_names.remove(piece2.name)
            pieces_eliminated.append(piece2.name)

            print(
                f"  - Combining parallel degenerate '{piece1.name}' with "
                f"'{piece2.name}' to form complete mesh '{piece1.name}'."
            )

            deselect_all_objects()

            bpy.context.view_layer.objects.active = piece1

            piece1.select_set(True)
            piece2.select_set(True)

            bpy.ops.object.join()

            make_piece_convex(piece1)

    return pieces_eliminated


def find_degenerate_combos(degenerate_piece_names):
    volumes = {}

    for piece_combo in combinations(degenerate_piece_names, 2):
        piece1_name, piece2_name = piece_combo
        piece1 = bpy.data.objects[piece1_name]
        piece2 = bpy.data.objects[piece2_name]

        if not volumes.get(piece1_name):
            volumes[piece1_name] = {}

        piece1_mesh = piece1.data
        piece1_bm = bmesh.new()
        piece1_bm.from_mesh(piece1_mesh)

        piece2_mesh = piece2.data
        piece2_bm = bmesh.new()
        piece2_bm.from_mesh(piece2_mesh)

        piece1_bm.faces.ensure_lookup_table()
        piece2_bm.faces.ensure_lookup_table()

        if (len(piece1_bm.faces) == 0) or (len(piece2_bm.faces) == 0):
            continue

        piece1_face = piece1_bm.faces[0]
        piece2_face = piece2_bm.faces[0]

        combo_angle_radians = piece1_face.normal.angle(piece2_face.normal)
        combo_angle_degrees = int(round(degrees(combo_angle_radians)))

        # We only combine faces that are parallel to each other
        if combo_angle_degrees in [0, 180]:
            combo_volume = convex_volume(piece1, piece2)

            volumes[piece1.name][piece2.name] = combo_volume

    return volumes


def eliminate_tiny_pieces(degenerate_piece_names, min_volume=0.1):
    eliminated_piece_names = []

    tiny_piece_names = [
        n for n in degenerate_piece_names
        if n not in eliminated_piece_names
           and convex_volume(bpy.data.objects.get(n)) < min_volume
    ]

    print("")
    print(f"Total remaining tiny pieces: {len(tiny_piece_names)}")

    # Delete tiny pieces that are too small to be useful
    for tiny_piece_name in tiny_piece_names:
        print(f"  - Eliminating tiny piece '{tiny_piece_name}'...")

        tiny_piece = bpy.data.objects[tiny_piece_name]

        bpy.data.objects.remove(tiny_piece, do_unlink=True)
        eliminated_piece_names.append(tiny_piece_name)

    print("")

    return eliminated_piece_names


def make_piece_convex(ob, min_volume=0.1):
    print(
        f"  - Attempting to make '{ob.name}' into a closed, convex "
        f"shape."
    )

    volume_before = convex_volume(ob)

    make_convex_hull(ob)

    volume_after = convex_volume(ob)
    volume_delta = abs(volume_after - volume_before)

    # If the volume of the piece is very small when we tried making it convex,
    # then it's degenerate -- it's a plane or something flat that we need to
    # remove.
    is_degenerate = (volume_after < min_volume)

    print(f"    - Volume before: {volume_before}")
    print(f"    - Volume after: {volume_after}")
    print(f"    - Volume delta: {volume_delta}")
    print(f"    - Is degenerate: {is_degenerate}")

    return not is_degenerate


def make_convex_hull(ob):
    deselect_all_objects()

    bpy.context.view_layer.objects.active = ob
    ob.select_set(True)

    bpy.ops.object.mode_set(mode='EDIT')

    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.convex_hull()

    mesh = ob.data
    bm = bmesh.from_edit_mesh(mesh)

    # Clean-up unnecessary edges
    bmesh.ops.dissolve_limit(
        bm,
        angle_limit=radians(5),
        verts=bm.verts,
        edges=bm.edges,
    )

    deselect_all_objects()


def have_common_normal(e1, e2):
    e1_normals = map(lambda f: f.normal, e1.link_faces)
    e2_normals = map(lambda f: f.normal, e2.link_faces)

    common_normals = [n for n in e1_normals if n in e2_normals]

    return len(common_normals) > 0


def have_common_face(e1, e2):
    common_faces = [f for f in e1.link_faces if f in e2.link_faces]

    return len(common_faces) > 0


# From https://blenderartists.org/t/finding-the-angle-between-edges-in-a-mesh-using-python/510618/2
def calc_edge_angle2(e1, e2):
    e1_vector = Vector(e1.verts[0].co) - Vector(e1.verts[1].co)
    e2_vector = Vector(e2.verts[0].co) - Vector(e2.verts[1].co)

    angle_in_radians = e1_vector.angle(e2_vector)

    return int(round(degrees(angle_in_radians)))


# From https://blender.stackexchange.com/a/203355/115505
def calc_edge_angle(e1, e2, face_normal):
    # project into XY plane,
    up = Vector((0, 0, 1))

    b = set(e1.verts).intersection(e2.verts).pop()
    a = e1.other_vert(b).co - b.co
    c = e2.other_vert(b).co - b.co
    a.negate()
    axis = a.cross(c).normalized()

    if axis.length < 1e-5:
        angle_in_radians = pi  # inline vert

    else:
        if axis.dot(face_normal) < 0:
            axis.negate()

        M = axis.rotation_difference(up).to_matrix().to_4x4()

        a = (M @ a).xy.normalized()
        c = (M @ c).xy.normalized()

        angle_in_radians = pi - atan2(a.cross(c), a.dot(c))

    return int(round(degrees(angle_in_radians)))


def convex_volume(*obs):
    meshes = []
    verts = []

    for ob in obs:
        mesh = ob.data
        bm = bmesh.new()

        bm.from_mesh(mesh)

        bm.verts.ensure_lookup_table()
        bm.edges.ensure_lookup_table()
        bm.faces.ensure_lookup_table()

        # Prevent early garbage collection.
        meshes.append(bm)

        geom = list(bm.verts) + list(bm.edges) + list(bm.faces)

        for g in geom:
            if hasattr(g, "verts"):
                verts.extend(v.co for v in g.verts)
            else:
                verts.append(g.co)

    return build_volume_from_verts(verts)


def build_volume_from_verts(verts):
    # Based on code from:
    # https://blender.stackexchange.com/questions/107357/how-to-find-if-geometry-linked-to-an-edge-is-coplanar
    origin = sum(verts, Vector((0, 0, 0))) / len(verts)
    bm = bmesh.new()

    for v in verts:
        bm.verts.new(v - origin)

    bmesh.ops.convex_hull(bm, input=bm.verts)

    return bm.calc_volume()


def get_global_origin(ob):
    local_bbox_center = 0.125 * sum((Vector(b) for b in ob.bound_box), Vector())

    return ob.matrix_world @ local_bbox_center


def deselect_all_objects():
    ensure_object_mode()
    bpy.ops.object.select_all(action='DESELECT')


def clear_file():
    # Clear all objects from the scene
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
    for i in range(len(ob.material_slots)):
        ob.active_material_index = i
        bpy.ops.object.material_slot_remove()


def remove_all_uv_maps(ob):
    uv_layers = ob.data.uv_layers
    uv_layers_to_remove = uv_layers[:]

    while uv_layers_to_remove:
        uv_layers.remove(uv_layers_to_remove.pop())


def rename_pieces(object_name, name_skiplist=None):
    if name_skiplist is None:
        name_skiplist = []

    for duplicate_name, old_index_str, new_index in dupe_name_sequence(object_name, name_skiplist):
        piece = bpy.data.objects.get(duplicate_name)

        if not piece:
            break

        old_name = piece.name
        new_name = re.sub(fr"(?:01)?\.{old_index_str}$", f"{new_index:02d}", piece.name)

        if old_name != new_name:
            print(f"Renaming piece '{old_name}' to '{new_name}'.")
            piece.name = new_name


def name_duplicates_of(ob):
    duplicates = []

    for duplicate_name, _, _ in dupe_name_sequence(ob.name):
        piece = bpy.data.objects.get(duplicate_name)

        if not piece:
            break
        else:
            duplicates.append(piece)

    return duplicates


def dupe_name_sequence(base_name, skiplist=None):
    if skiplist is None:
        skiplist = []

    yield base_name, "", 1

    new_index = 1

    for old_name_index in count(start=1):
        old_index_str = f"{old_name_index:03d}"
        duplicate_name = f"{base_name}.{old_index_str}"

        if duplicate_name in skiplist:
            continue
        else:
            new_index = new_index + 1

            yield duplicate_name, old_index_str, new_index


def ensure_object_mode():
    if bpy.context.active_object is not None and bpy.context.active_object.mode != 'OBJECT':
        bpy.ops.object.mode_set(mode='OBJECT')


def status_print(msg):
    formatted_msg = "%-120s" % msg
    sys.stdout.write(formatted_msg + (chr(8) * len(formatted_msg)))
    sys.stdout.flush()


clear_file()
import_fbx(fbx_path)
cleanup_scene()
setup_uvs()
# apply_uv_grid()
generate_collision()
export_all_collections_to_fbx()

print("Done!")
