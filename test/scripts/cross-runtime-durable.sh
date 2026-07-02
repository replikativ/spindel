#!/usr/bin/env bash
# DURABLE cross-RUNTIME proof: a JVM kabel server holding a FILE-backed G-Set
# replicates it (nodes over konserve-sync + value over signal-sync, ONE fressian
# serializer) to a cljs(node) client backed by a konserve node-filestore. The client
# reconstructs #{:alpha :beta} AND proves it survived a COLD RESTART (reopen the
# node-filestore from disk). Success = client exits 0.
set -uo pipefail
cd "$(dirname "$0")/../.."
OUT=$(mktemp -d)
rm -rf /tmp/xrt-dur-server /tmp/xrt-dur-client
echo "compiling durable node client..."
npx shadow-cljs compile cross-runtime-durable-client > "$OUT/compile.out" 2>&1 || { echo "client compile failed"; tail -30 "$OUT/compile.out"; exit 9; }
echo "starting JVM durable server..."
clojure -M:test:ylocal:cross-durable-server > "$OUT/server.out" 2>&1 &
SERVER_PID=$!
for i in $(seq 1 90); do grep -q "XRT-DUR-SERVER-UP" "$OUT/server.out" 2>/dev/null && break; sleep 1; done
grep -q "XRT-DUR-SERVER-UP" "$OUT/server.out" 2>/dev/null || { echo "server never came up"; tail -20 "$OUT/server.out"; kill $SERVER_PID 2>/dev/null; exit 8; }
echo "running durable node client..."
node target/cross-runtime-durable-client.js > "$OUT/client.out" 2>&1
CLIENT_EXIT=$?
kill $SERVER_PID 2>/dev/null; wait $SERVER_PID 2>/dev/null
echo "=== client ==="; grep -aE "XRT-DUR-CLIENT|CLIENT-|STACK" "$OUT/client.out"
echo "=== server ==="; grep -aE "XRT-DUR-SERVER" "$OUT/server.out" | tail -2
echo "CLIENT_EXIT=$CLIENT_EXIT"
if [ "$CLIENT_EXIT" = 0 ]; then
  echo "CROSS-RUNTIME-DURABLE-OK"
else
  echo "CROSS-RUNTIME-DURABLE-FAILED"; echo "--- client tail ---"; tail -25 "$OUT/client.out"
fi
rm -rf "$OUT" /tmp/xrt-dur-server /tmp/xrt-dur-client
[ "$CLIENT_EXIT" = 0 ]
