# @generated
# To regenerate this file run fbcode//glean/schema/gen/sync
from typing import Optional, Tuple, Union
import json
from thrift.py3 import Struct
from glean.schema.py.glean_schema_predicate import GleanSchemaPredicate


from glean.schema.codemarkupcxx.types import (
    CxxCxxFileEntityXRefLocations,
    CxxCxxContainsChildEntity,
    CxxCxxEntityUses,
    CxxCxxEntityKind,
    CxxCxxResolveLocation,
    CxxCxxDefToDeclFamilyXRefTargetLocation,
    CxxCxxEntityLocation,
    CxxCxxVisibility,
    CxxCxxFileEntityXMapVariableXRefDeclLocations,
    CxxCxxDeclToDefXRefTargetLocation,
    CxxCxxAnnotation,
    CxxCxxFileEntityFixedXRefLocations,
    CxxCxxResolveDeclarationToEntity,
    CxxCxxXRefTargetLocation,
    CxxCxxFileEntityTraceFixedXRefLocations,
    CxxCxxEntityInfo,
    CxxCxxFileEntityTraceLocations,
    CxxCxxDeclInfo,
    CxxCxxResolveTraceLocation,
    CxxCxxFileEntityXMapFixedXRefLocations,
    CxxCxxFileEntityTraceDeclToDefXRefLocations,
    CxxCxxDeclKind,
    CxxCxxFileEntityXMapVariableXRefDeclToDefs,
)


class CodemarkupCxxCxxFileEntityXRefLocations(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxFileEntityXRefLocations.4 {{ file = _, xref = _, entity = _ }}", CxxCxxFileEntityXRefLocations

  @staticmethod
  def angle_query(*, file: Optional[Tuple[()]] = None, xref: Optional[Tuple[()]] = None, entity: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxFileEntityXRefLocations":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxContainsChildEntity(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxContainsChildEntity.4 {{ parent = _, child = _ }}", CxxCxxContainsChildEntity

  @staticmethod
  def angle_query(*, parent: Optional[Tuple[()]] = None, child: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxContainsChildEntity":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxEntityUses(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxEntityUses.4 {{ target = _, file = _, span = _ }}", CxxCxxEntityUses

  @staticmethod
  def angle_query(*, target: Optional[Tuple[()]] = None, file: Optional[Tuple[()]] = None, span: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxEntityUses":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxEntityKind(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxEntityKind.4 {{ entity = _, kind = _ }}", CxxCxxEntityKind

  @staticmethod
  def angle_query(*, entity: Optional[Tuple[()]] = None, kind: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxEntityKind":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxResolveLocation(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxResolveLocation.4 {{ location = _, entity = _ }}", CxxCxxResolveLocation

  @staticmethod
  def angle_query(*, location: Optional[Tuple[()]] = None, entity: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxResolveLocation":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxDefToDeclFamilyXRefTargetLocation(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxDefToDeclFamilyXRefTargetLocation.4 {{ decl = _, entity = _, location = _ }}", CxxCxxDefToDeclFamilyXRefTargetLocation

  @staticmethod
  def angle_query(*, decl: Optional[Tuple[()]] = None, entity: Optional[Tuple[()]] = None, location: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxDefToDeclFamilyXRefTargetLocation":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxEntityLocation(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxEntityLocation.4 {{ entity = _, location = _ }}", CxxCxxEntityLocation

  @staticmethod
  def angle_query(*, entity: Optional[Tuple[()]] = None, location: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxEntityLocation":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxVisibility(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxVisibility.4 {{ entity = _, visibility = _ }}", CxxCxxVisibility

  @staticmethod
  def angle_query(*, entity: Optional[Tuple[()]] = None, visibility: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxVisibility":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxFileEntityXMapVariableXRefDeclLocations(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxFileEntityXMapVariableXRefDeclLocations.4 {{ trace = _, source = _, location = _ }}", CxxCxxFileEntityXMapVariableXRefDeclLocations

  @staticmethod
  def angle_query(*, trace: Optional[Tuple[()]] = None, source: Optional[Tuple[()]] = None, location: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxFileEntityXMapVariableXRefDeclLocations":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxDeclToDefXRefTargetLocation(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxDeclToDefXRefTargetLocation.4 {{ decl = _, entity = _, location = _ }}", CxxCxxDeclToDefXRefTargetLocation

  @staticmethod
  def angle_query(*, decl: Optional[Tuple[()]] = None, entity: Optional[Tuple[()]] = None, location: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxDeclToDefXRefTargetLocation":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxAnnotation(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxAnnotation.4 {{ entity = _, anns = _ }}", CxxCxxAnnotation

  @staticmethod
  def angle_query(*, entity: Optional[Tuple[()]] = None, anns: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxAnnotation":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxFileEntityFixedXRefLocations(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxFileEntityFixedXRefLocations.4 {{ file = _, xref = _, entity = _ }}", CxxCxxFileEntityFixedXRefLocations

  @staticmethod
  def angle_query(*, file: Optional[Tuple[()]] = None, xref: Optional[Tuple[()]] = None, entity: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxFileEntityFixedXRefLocations":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxResolveDeclarationToEntity(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxResolveDeclarationToEntity.4 {{ decl = _, entity = _ }}", CxxCxxResolveDeclarationToEntity

  @staticmethod
  def angle_query(*, decl: Optional[Tuple[()]] = None, entity: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxResolveDeclarationToEntity":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxXRefTargetLocation(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxXRefTargetLocation.4 {{ target = _, entity = _, location = _ }}", CxxCxxXRefTargetLocation

  @staticmethod
  def angle_query(*, target: Optional[Tuple[()]] = None, entity: Optional[Tuple[()]] = None, location: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxXRefTargetLocation":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxFileEntityTraceFixedXRefLocations(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxFileEntityTraceFixedXRefLocations.4 {{ file = _, trace = _, xref = _, entity = _ }}", CxxCxxFileEntityTraceFixedXRefLocations

  @staticmethod
  def angle_query(*, file: Optional[Tuple[()]] = None, trace: Optional[Tuple[()]] = None, xref: Optional[Tuple[()]] = None, entity: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxFileEntityTraceFixedXRefLocations":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxEntityInfo(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxEntityInfo.4 {{ entity = _, info = _ }}", CxxCxxEntityInfo

  @staticmethod
  def angle_query(*, entity: Optional[Tuple[()]] = None, info: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxEntityInfo":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxFileEntityTraceLocations(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxFileEntityTraceLocations.4 {{ file = _, trace = _, location = _, entity = _ }}", CxxCxxFileEntityTraceLocations

  @staticmethod
  def angle_query(*, file: Optional[Tuple[()]] = None, trace: Optional[Tuple[()]] = None, location: Optional[Tuple[()]] = None, entity: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxFileEntityTraceLocations":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxDeclInfo(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxDeclInfo.4 {{ decl = _, info = _ }}", CxxCxxDeclInfo

  @staticmethod
  def angle_query(*, decl: Optional[Tuple[()]] = None, info: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxDeclInfo":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxResolveTraceLocation(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxResolveTraceLocation.4 {{ trace = _, location = _, entity = _ }}", CxxCxxResolveTraceLocation

  @staticmethod
  def angle_query(*, trace: Optional[Tuple[()]] = None, location: Optional[Tuple[()]] = None, entity: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxResolveTraceLocation":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxFileEntityXMapFixedXRefLocations(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxFileEntityXMapFixedXRefLocations.4 {{ trace = _, xref = _, entity = _ }}", CxxCxxFileEntityXMapFixedXRefLocations

  @staticmethod
  def angle_query(*, trace: Optional[Tuple[()]] = None, xref: Optional[Tuple[()]] = None, entity: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxFileEntityXMapFixedXRefLocations":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxFileEntityTraceDeclToDefXRefLocations(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxFileEntityTraceDeclToDefXRefLocations.4 {{ file = _, trace = _, xref = _, entity = _ }}", CxxCxxFileEntityTraceDeclToDefXRefLocations

  @staticmethod
  def angle_query(*, file: Optional[Tuple[()]] = None, trace: Optional[Tuple[()]] = None, xref: Optional[Tuple[()]] = None, entity: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxFileEntityTraceDeclToDefXRefLocations":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxDeclKind(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxDeclKind.4 {{ decl = _, kind = _ }}", CxxCxxDeclKind

  @staticmethod
  def angle_query(*, decl: Optional[Tuple[()]] = None, kind: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxDeclKind":
    raise Exception("this function can only be called from @angle_query")

class CodemarkupCxxCxxFileEntityXMapVariableXRefDeclToDefs(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"codemarkup.cxx.CxxFileEntityXMapVariableXRefDeclToDefs.4 {{ trace = _, source = _, entity = _, location = _ }}", CxxCxxFileEntityXMapVariableXRefDeclToDefs

  @staticmethod
  def angle_query(*, trace: Optional[Tuple[()]] = None, source: Optional[Tuple[()]] = None, entity: Optional[Tuple[()]] = None, location: Optional[Tuple[()]] = None) -> "CodemarkupCxxCxxFileEntityXMapVariableXRefDeclToDefs":
    raise Exception("this function can only be called from @angle_query")


