package bergdb.common;

/**
 * Counts how often something happens in occurrences per second. An exponentially decreasing mean is
 * used. See http://en.wikipedia.org/wiki/Exponential_decay.
 * 
 * @author Frans Lundberg
 */
public class FrequencySensor {
    /** Half life in seconds. */
    private double halfLife;

    /** Current value. */
    private double value;

    /** The time at which the value was last computed. */
    private long valueTime;

    /**
     * A new counter. To measure frequency accurately, the average time between events should be
     * many times smaller than halfLife. The frequency value estimate start at 0.0.
     * 
     * @param halfLife
     *            Half life for averaging in seconds.
     */
    public FrequencySensor(double halfLife) {
        if (halfLife <= 0.0) {
            throw new IllegalArgumentException();
        }
        this.halfLife = halfLife;
        this.value = 0.0;
        this.valueTime = System.nanoTime();
    }

    /**
     * Call this every time an event occurs.
     */
    public synchronized void tick() {
        tick(System.nanoTime());
    }

    /**
     * Call this method every time an event occurs. This method takes a nano second time value.
     * Useful for deterministic testing and other scenarios when the system nano time
     * (System.nanoTime()) should not be used.
     * 
     * @param nanoTime
     *            Time in nano seconds.
     */
    public synchronized void tick(long nanoTime) {
        long now = nanoTime;
        double diff = 1e-9 * Math.abs(now - valueTime); // time diff in secs
        double decayFactor = Math.pow(2.0, -diff / halfLife);

        // frequency estimate since last event is 1.0 / <time since last event>
        double fEstimate = 1.0 / diff;

        this.value = decayFactor * this.value + (1.0 - decayFactor) * fEstimate;
        this.valueTime = now;
    }

    /**
     * Returns the frequency in occurrences per second.
     */
    public synchronized double getFrequency() {
        return getFrequency(System.nanoTime());
    }

    public synchronized double getFrequency(long nanoTime) {
        double diff = 1e-9 * Math.abs(nanoTime - valueTime);
        double decayFactor = Math.pow(2.0, -diff / halfLife);
        return value * decayFactor;
    }

    public String toString() {
        return "f=" + getFrequency();
    }

    /** For testing. */
    public static void main(String[] args) throws Exception {
        final FrequencySensor f1 = new FrequencySensor(1.0);

        new Thread(new Runnable() {
            public void run() {
                for (int i = 0; i < 2000; i++) {
                    f1.tick();
                    try {
                        Thread.sleep(10);
                    } catch (InterruptedException e) {
                        throw new RuntimeException(e);
                    }
                }
            }
        }).start();

        for (int i = 0; i < 30; i++) {
            System.out.println(f1);
            Thread.sleep(1000);
        }
    }
}

/*
 * http://en.wikipedia.org/wiki/Exponential_decay. N(t) = N0 * 2 ^ (-t / t_half)
 * 
 * Our strategy is to be keep only two numbers and still get a current estimate of frequency. value
 * is the frequency estimate at time valueTime. The frequency estimate any time in the future is:
 * 
 * decayFactor = 2 ^ (-(now - valueTime) / halfLife) valueNow = value * decayFactor
 * 
 * When an event occurs, we update the value by a weighted average based on the old frequency value
 * and the new estimate which is:
 * 
 * fEstimate = 1.0 / <time elapsed since last event>
 * 
 * The weighted average is:
 * 
 * this.value = decayFactor * this.value + (1.0 - decayFactor) * fEstimate;
 * 
 * The decayFactor is computed from time since last event and the halfLife constant.
 */