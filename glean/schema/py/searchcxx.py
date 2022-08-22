# @generated
# To regenerate this file run fbcode//glean/schema/gen/sync
from typing import Tuple, Type, Union, TypeVar
import json
from thrift.py3 import Struct
from glean.schema.py.glean_schema_predicate import GleanSchemaPredicate


from glean.schema.searchcxx.types import (
    CxxSearchBySelector,
    CxxSearchByScope,
    CxxQueryToQName,
    CxxGlobalDeclarationWithName,
    CxxDeclIsDefn,
    CxxQueryToScope,
    CxxSearchByNameAndScope,
    CxxEntityUses,
    CxxQueryToNSQName,
)


class SearchCxxSearchBySelector(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"search.cxx.SearchBySelector.5 {{ selector = _, entity = _ }}", CxxSearchBySelector

  @staticmethod
  def angle_query(*, selector: Tuple[()], entity: Tuple[()]) -> "SearchCxxSearchBySelector":
    raise Exception("this function can only be called from @angle_query")

class SearchCxxSearchByScope(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"search.cxx.SearchByScope.5 {{ scope = _, entity = _ }}", CxxSearchByScope

  @staticmethod
  def angle_query(*, scope: Tuple[()], entity: Tuple[()]) -> "SearchCxxSearchByScope":
    raise Exception("this function can only be called from @angle_query")

class SearchCxxQueryToQName(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"search.cxx.QueryToQName.5 {{ query = _, scope = _ }}", CxxQueryToQName

  @staticmethod
  def angle_query(*, query: Tuple[()], scope: Tuple[()]) -> "SearchCxxQueryToQName":
    raise Exception("this function can only be called from @angle_query")

class SearchCxxGlobalDeclarationWithName(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"search.cxx.GlobalDeclarationWithName.5 {{ name = _, decl = _ }}", CxxGlobalDeclarationWithName

  @staticmethod
  def angle_query(*, name: Tuple[()], decl: Tuple[()]) -> "SearchCxxGlobalDeclarationWithName":
    raise Exception("this function can only be called from @angle_query")

class SearchCxxDeclIsDefn(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"search.cxx.DeclIsDefn.5 {{ decl = _, defn = _ }}", CxxDeclIsDefn

  @staticmethod
  def angle_query(*, decl: Tuple[()], defn: Tuple[()]) -> "SearchCxxDeclIsDefn":
    raise Exception("this function can only be called from @angle_query")

class SearchCxxQueryToScope(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"search.cxx.QueryToScope.5 {{ query = _, scope = _ }}", CxxQueryToScope

  @staticmethod
  def angle_query(*, query: Tuple[()], scope: Tuple[()]) -> "SearchCxxQueryToScope":
    raise Exception("this function can only be called from @angle_query")

class SearchCxxSearchByNameAndScope(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"search.cxx.SearchByNameAndScope.5 {{ name = _, scope = _, entity = _ }}", CxxSearchByNameAndScope

  @staticmethod
  def angle_query(*, name: Tuple[()], scope: Tuple[()], entity: Tuple[()]) -> "SearchCxxSearchByNameAndScope":
    raise Exception("this function can only be called from @angle_query")

class SearchCxxEntityUses(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"search.cxx.EntityUses.5 {{ entity = _, uses = _ }}", CxxEntityUses

  @staticmethod
  def angle_query(*, entity: Tuple[()], uses: Tuple[()]) -> "SearchCxxEntityUses":
    raise Exception("this function can only be called from @angle_query")

class SearchCxxQueryToNSQName(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"search.cxx.QueryToNSQName.5 {{ query = _, scope = _ }}", CxxQueryToNSQName

  @staticmethod
  def angle_query(*, query: Tuple[()], scope: Tuple[()]) -> "SearchCxxQueryToNSQName":
    raise Exception("this function can only be called from @angle_query")


