import Lake

open Lake DSL

package «bms-constructible-bridge»

require YesMetaZFC from ".."
require «lean-constructible-universe» from git
  "https://github.com/05-02-07/lean-constructible-universe.git" @
    "7f5a7d03d63d9769172f17350bbe8303996e5b53"

@[default_target]
lean_lib BMSConstructibleBridge
