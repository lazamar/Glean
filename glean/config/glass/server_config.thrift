// @generated SignedSource<<812fa5b4bf04d297580efd96db6d7c44>>
// DO NOT EDIT THIS FILE MANUALLY!
// This file is a mechanical copy of the version in the configerator repo. To
// modify it, edit the copy in the configerator repo instead and copy it over by
// running the following in your fbcode directory:
//
// configerator-thrift-updater glean/glass/server_config.thrift

namespace hs Glean.Glass

struct ServerConfig {
  1: i32 port; # glass server listening port
}
