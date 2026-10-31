package bench;

import java.lang.instrument.ClassFileTransformer;
import java.lang.instrument.Instrumentation;
import java.security.ProtectionDomain;
import java.util.concurrent.atomic.AtomicLong;

/** Counts byte arrays actually defined by the benchmark's eval compiler. */
public final class BytecodeAgent {
    private static final AtomicLong classes = new AtomicLong();
    private static final AtomicLong bytes = new AtomicLong();
    private static final AtomicLong maxFilename = new AtomicLong();

    public static void premain(String options, Instrumentation instrumentation) {
        instrumentation.addTransformer(new ClassFileTransformer() {
            @Override
            public byte[] transform(ClassLoader loader, String name, Class<?> previous,
                                    ProtectionDomain domain, byte[] bytecode) {
                if (name != null && name.startsWith("collection_bench$")) {
                    classes.incrementAndGet();
                    bytes.addAndGet(bytecode.length);
                    long length = name.substring(name.lastIndexOf('/') + 1).length() + 6;
                    maxFilename.accumulateAndGet(length, Math::max);
                }
                return null;
            }
        });
    }

    public static void reset() {
        classes.set(0);
        bytes.set(0);
        maxFilename.set(0);
    }

    public static long[] snapshot() {
        return new long[] {classes.get(), bytes.get(), maxFilename.get()};
    }
}
