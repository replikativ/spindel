#!/usr/bin/env bash
# Cross-RUNTIME bidirectional sync proof: a JVM kabel server + a cljs(node) kabel
# client converge a G-Set over one real websocket. Both must exit 0:
#   client exit 0 => it received the server's :jvm (server->client)
#   server exit 0 => it received the client's :cljs (client->server)
set -uo pipefail
cd "$(dirname "$0")/../.."
OUT=$(mktemp -d)
echo "compiling node client..."
npx shadow-cljs compile cross-runtime-client >/dev/null 2>&1 || { echo "client compile failed"; exit 9; }
echo "starting JVM server..."
clojure -M:test:cross-server > "$OUT/server.out" 2>&1 &
SERVER_PID=$!
for i in $(seq 1 90); do grep -q "CROSS-RUNTIME-SERVER-UP" "$OUT/server.out" 2>/dev/null && break; sleep 1; done
echo "running node client..."
node target/cross-runtime-client.js > "$OUT/client.out" 2>&1
CLIENT_EXIT=$?
wait $SERVER_PID; SERVER_EXIT=$?
echo "=== client ==="; grep -aE "CLIENT-" "$OUT/client.out"
echo "=== server ==="; grep -aE "SERVER-|CROSS-RUNTIME-SERVER-UP" "$OUT/server.out" | tail -3
echo "CLIENT_EXIT=$CLIENT_EXIT SERVER_EXIT=$SERVER_EXIT"
[ "$CLIENT_EXIT" = 0 ] && [ "$SERVER_EXIT" = 0 ] && echo "CROSS-RUNTIME-BIDIRECTIONAL-OK" || echo "CROSS-RUNTIME-FAILED"
rm -rf "$OUT"
