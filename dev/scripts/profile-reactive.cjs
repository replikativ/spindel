// node dev/scripts/profile-reactive.cjs <compiled-benchmark.js> <output-prefix>
// Select one engine/graph with SPINDEL_COMPARE_* environment variables.
// Includes setup and warmup; use unprofiled runs for throughput comparisons.
// Allocation samples include collected objects, not just survivors:
// https://chromedevtools.github.io/devtools-protocol/tot/HeapProfiler/#method-startSampling
const { Session } = require('node:inspector');
const fs = require('node:fs');
const path = require('node:path');

async function main() {
  const [program, output] = process.argv.slice(2);
  if (!program || !output) throw new Error('Expected benchmark path and output prefix');
  const session = new Session();
  const post = (method, params = {}) => new Promise((resolve, reject) =>
    session.post(method, params, (error, result) => error ? reject(error) : resolve(result)));
  session.connect();
  try {
    await post('Profiler.enable');
    await post('Profiler.start');
    await post('HeapProfiler.startSampling', {
      samplingInterval: 16384,
      includeObjectsCollectedByMajorGC: true,
      includeObjectsCollectedByMinorGC: true
    });
    process.env.SPINDEL_COMPARE_PROFILED = '1';
    try {
      require(path.resolve(program));
    } finally {
      const heap = await post('HeapProfiler.stopSampling');
      const cpu = await post('Profiler.stop');
      fs.writeFileSync(`${output}.heapprofile`, JSON.stringify(heap.profile));
      fs.writeFileSync(`${output}.cpuprofile`, JSON.stringify(cpu.profile));
      fs.writeFileSync(`${output}.meta.json`, JSON.stringify({
        program: path.resolve(program), versions: process.versions,
        scope: 'module initialization, setup, warmup and measured updates',
        settings: Object.fromEntries(Object.entries(process.env)
          .filter(([key]) => key.startsWith('SPINDEL_COMPARE_')))
      }, null, 2));
    }
  } finally {
    session.disconnect();
  }
}
main().catch(error => { console.error(error); process.exitCode = 1; });
