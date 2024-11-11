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
import re
import sys
import time

from collections import OrderedDict
from itertools import count
from math import radians
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

unwanted_element_regex_str = r"^.+((_(Door|Window)_\d{2})|(Ladder.*))$"

prefix_regex_str = \
    r"^(?P<Prefix>(?:Closet_)?(?:Conduit(?:_\d{2})?_)?" \
    r"(?:CeilingTrim|Ceiling|Floor|Post|Roof|Slab|StairWall|Stairs|Tub_Shelf" \
    r"|WallPanel|Wall)(?:_\d{2})?)"

basic_collision_regex_str = r"^.+_(?:(?:Wall|Post|StairWall|.*PorchCeiling)(?:_\d{2})?)$"
slab_collision_regex_str = r"^House_Floor_\d{2}_Slab$"

wall_opening_regex_str = r"^$NAME$_(?:(Door|Window)_[0-9]{2}_)?Opening(?:_[0-9]{2})?$"
floor_opening_regex_str = r"^.+_Stairs_Opening$"

element_regex = re.compile(element_regex_str)
unwanted_element_regex = re.compile(unwanted_element_regex_str)
prefix_regex = re.compile(prefix_regex_str)

basic_collision_regex = re.compile(basic_collision_regex_str)
slab_collision_regex = re.compile(slab_collision_regex_str)

floor_opening_regex = re.compile(floor_opening_regex_str)


def import_fbx(path):
    bpy.ops.import_scene.fbx(filepath=path)


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
        status_print(f"  - Exporting collection '{coll.name}' to FBX...")

        # Select only objects in the current collection.
        deselect_all_objects()

        for obj in coll.all_objects:
            obj.select_set(True)

        try:
            bpy.ops.export_scene.fbx(
                filepath=str(Path(bpy.data.filepath).parent / f"{coll.name}.fbx"),
                use_selection=True,
                mesh_smooth_type='FACE',
                use_tspace=True,
                bake_space_transform=True,
                check_existing=False
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

        decompose_into_convex_parts(collision_ob)

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
        decompose_into_convex_parts(collision_ob)

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


def make_all_faces_convex(ob):
    bpy.context.view_layer.objects.active = ob
    bpy.ops.object.mode_set(mode='EDIT')

    # This is what actually defines the new geometry -- Blender creates the
    # convex shapes we need to split by.
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.vert_connect_concave()
    bpy.ops.mesh.select_all(action='DESELECT')


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


def decompose_into_convex_parts(ob, max_iterations=5, volume_threshold=0.01):
    """
    Decompose an object into convex parts using convex hulls and boolean operations.

    :param ob: The input object to decompose.
    :param max_iterations: The maximum number of decomposition iterations.
    :param volume_threshold: Minimum volume threshold to consider a part.
    """
    ob.select_set(True)
    bpy.context.view_layer.objects.active = ob

    for i in range(max_iterations):
        if is_convex(ob):
            # Stop if the object is already convex.
            print(f"  - {ob.name} is already convex.")
            break

        convex_hull = create_convex_hull(ob)
        convex_hull.name = f"{ob.name}_convex_part_{i}"

        boundary_faces = identify_boundary_faces(ob, convex_hull)
        if not boundary_faces:
            # No more boundary faces to split on.
            break

        new_part = split_object(ob, boundary_faces)
        new_part.name = f"{ob.name}_part_{i}"

        if convex_volume(new_part) < volume_threshold:
            bpy.data.objects.remove(new_part)
            continue

    print(f"  - Convex decomposition of {ob.name} is complete.")


def is_convex(ob):
    """Check if the object is convex by verifying no internal faces violate convexity."""
    bm = bmesh.new()
    bm.from_mesh(ob.data)
    bm.faces.ensure_lookup_table()

    threshold_angle = math.radians(180)

    # Convex if no angles exceed the threshold.
    result = True

    for edge in bm.edges:
        linked_faces = edge.link_faces
        if len(linked_faces) == 2:  # Only consider pairs of adjacent faces
            angle = angle_between_face_normals(linked_faces[0], linked_faces[1])

            # Concave if angle exceeds threshold
            if angle > threshold_angle:
                result = False
                break

    bm.free()

    return result


def angle_between_face_normals(face1, face2):
    """
    Calculate the angle in radians between the normals of two given faces.

    Args:
        face1 (bmesh.types.BMFace): The first face.
        face2 (bmesh.types.BMFace): The second face.

    Returns:
        float: The angle in radians between the two face normals.
    """
    normal1 = face1.normal
    normal2 = face2.normal

    if normal1.length == 0 or normal2.length == 0:
      result = 0
    else:
      result = normal1.angle(normal2)

    return result


def create_convex_hull(ob):
    """Create and return a convex hull object around the provided object."""
    bpy.ops.object.mode_set(mode='OBJECT')
    ob.select_set(True)
    bpy.ops.object.duplicate()
    convex_hull = bpy.context.active_object
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.convex_hull()
    bpy.ops.object.mode_set(mode='OBJECT')

    return convex_hull


def identify_boundary_faces(ob, convex_hull, max_convex_deviation=0.001):
    """
    Identify boundary faces between an object and its convex hull,
    which can serve as split points for decomposition.
    """
    boundary_faces = []
    bm = bmesh.new()
    bm.from_mesh(ob.data)
    bm.faces.ensure_lookup_table()

    for face in bm.faces:
        face_center = face.calc_center_median()

        # Unpack the return values from closest_point_on_mesh
        found, closest_point, normal, index = convex_hull.closest_point_on_mesh(face_center)

        if found:
            closest_point_vector = closest_point

            # Calculate the distance
            distance = (face_center - closest_point_vector).length

            if distance > max_convex_deviation:
                boundary_faces.append(face)

    bm.free()
    return boundary_faces


def split_object(ob, boundary_faces):
    """
    Split the object using identified boundary faces. Creates a new object from the split part.
    """
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_all(action='DESELECT')

    for face in boundary_faces:
        face.select = True

    bpy.ops.mesh.separate(type='SELECTED')
    bpy.ops.object.mode_set(mode='OBJECT')

    return bpy.context.selected_objects[-1]  # Return new part after split


clear_file()
import_fbx(fbx_path)
cleanup_scene()
setup_uvs()
# apply_uv_grid()
generate_collision()
export_all_collections_to_fbx()

print("Done!")
