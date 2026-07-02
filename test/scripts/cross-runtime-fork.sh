#!/usr/bin/env bash
# Cross-RUNTIME FORK/MERGE proof: a cljs(node) peer runs the full
# fork-remote!→write→merge-fork-remote! lifecycle against a REAL local datahike
# (memory) system over one live websocket to a JVM kabel server, then publishes the
# merged item-names. Both must exit 0:
#   client exit 0 => its cljs datahike merge converged to #{trunk fork-edit}
#   server exit 0 => those merged names reached the JVM peer over the wire
set -uo pipefail
cd "$(dirname "$0")/../.."
OUT=$(mktemp -d)
echo "compiling node fork client..."
npx shadow-cljs compile cross-runtime-fork-client >"$OUT/compile.out" 2>&1 || { echo "client compile failed"; tail -30 "$OUT/compile.out"; exit 9; }
echo "starting JVM fork server..."
clojure -M:test:cross-fork-server > "$OUT/server.out" 2>&1 &
SERVER_PID=$!
for i in $(seq 1 90); do grep -q "CROSS-RUNTIME-FORK-SERVER-UP" "$OUT/server.out" 2>/dev/null && break; sleep 1; done
echo "running node fork client..."
node target/cross-runtime-fork-client.js > "$OUT/client.out" 2>&1
CLIENT_EXIT=$?
wait $SERVER_PID; SERVER_EXIT=$?
echo "=== client ==="; grep -aE "CLIENT-" "$OUT/client.out"
echo "=== server ==="; grep -aE "SERVER-|CROSS-RUNTIME-FORK-SERVER-UP" "$OUT/server.out" | tail -3
echo "CLIENT_EXIT=$CLIENT_EXIT SERVER_EXIT=$SERVER_EXIT"
[ "$CLIENT_EXIT" = 0 ] && [ "$SERVER_EXIT" = 0 ] && echo "CROSS-RUNTIME-FORK-MERGE-OK" || echo "CROSS-RUNTIME-FORK-MERGE-FAILED"
rm -rf "$OUT"
