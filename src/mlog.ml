open Printf

let verbose = false

let log = if verbose then stderr else open_out "debuglog"

let meprintf format = fprintf log format

let meprintf format = flush log ; meprintf format