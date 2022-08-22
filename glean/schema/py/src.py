# @generated
# To regenerate this file run fbcode//glean/schema/gen/sync
from typing import Tuple, Type, Union, TypeVar
import json
from thrift.py3 import Struct
from glean.schema.py.glean_schema_predicate import GleanSchemaPredicate


from glean.schema.src.types import (
    IndexFailure,
    ByteSpanContains,
    File,
    FileLanguage,
    FileLines,
)


class SrcIndexFailure(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"src.IndexFailure.1 {{ file = _, reason = _, details = _ }}", IndexFailure

  @staticmethod
  def angle_query(*, file: Tuple[()], reason: Tuple[()], details: str) -> "SrcIndexFailure":
    raise Exception("this function can only be called from @angle_query")

class SrcByteSpanContains(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"src.ByteSpanContains.1 {{ byteSpan = _, contains = _ }}", ByteSpanContains

  @staticmethod
  def angle_query(*, byteSpan: Tuple[()], contains: Tuple[()]) -> "SrcByteSpanContains":
    raise Exception("this function can only be called from @angle_query")

class SrcFile(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"src.File.1 {json.dumps(key)}", File

  @staticmethod
  def angle_query(*, arg: str) -> "SrcFile":
    raise Exception("this function can only be called from @angle_query")

class SrcFileLanguage(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"src.FileLanguage.1 {{ file = _, language = _ }}", FileLanguage

  @staticmethod
  def angle_query(*, file: Tuple[()], language: Tuple[()]) -> "SrcFileLanguage":
    raise Exception("this function can only be called from @angle_query")

class SrcFileLines(GleanSchemaPredicate):
  @staticmethod
  def build_angle(key: Union[int, bool, str, Tuple[()]]) -> Tuple[str, Struct]:
    return f"src.FileLines.1 {{ file = _, lengths = _, endsInNewline = _, hasUnicodeOrTabs = _ }}", FileLines

  @staticmethod
  def angle_query(*, file: Tuple[()], lengths: Tuple[()], endsInNewline: bool, hasUnicodeOrTabs: bool) -> "SrcFileLines":
    raise Exception("this function can only be called from @angle_query")


