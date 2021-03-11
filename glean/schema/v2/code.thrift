// To re-generate this file:
//
//   ./glean/schema/sync
//
// @generated
// @nolint

include "glean/if/glean.thrift"
include "glean/schema/v2/builtin.thrift"
include "glean/schema/v2/code_cxx.thrift"
include "glean/schema/v2/code_flow.thrift"
include "glean/schema/v2/code_hack.thrift"
include "glean/schema/v2/code_hs.thrift"
include "glean/schema/v2/code_java.thrift"
include "glean/schema/v2/code_python.thrift"
include "glean/schema/v2/pp1.thrift"

namespace cpp2 facebook.glean.schema.code
namespace hs Glean.Schema
namespace php glean_schema_code
namespace py glean.schema.code
namespace py3 glean.schema
namespace java.swift com.facebook.glean.schema.code
namespace rust glean_schema_code

hs_include "glean/schema/v2/code_include.hs"
const map<string, i64> PREDICATE_VERSIONS = {
}


union Entity {
  1: code_cxx.Entity cxx;
  2: pp1.Define pp;
  3: code_java.Entity java;
  4: code_hs.Entity hs;
  5: code_python.Entity python;
  6: code_hack.Entity hack;
  7: code_flow.Entity flow;
} (hs.nonempty)

union Entity_9 {
  1: code_cxx.Entity cxx;
  2: pp1.Define pp;
  3: code_java.Entity java;
  4: code_hs.Entity hs;
  5: code_python.Entity python;
  6: code_hack.Entity hack;
} (hs.nonempty)

union Entity_8 {
  1: code_cxx.Entity cxx;
  2: pp1.Define pp;
  3: code_java.Entity_2 java;
  4: code_hs.Entity hs;
  5: code_python.Entity python;
  6: code_hack.Entity hack;
} (hs.nonempty)
