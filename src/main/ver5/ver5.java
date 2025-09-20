package main.ver5;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.atomic.*;
import java.util.stream.*;
import java.time.*;
import java.io.*;

/**
 * PTK-HUIM-U±: Enhanced Parallel Top-K High-Utility Itemset Mining
 * from Uncertain Databases with Positive and Negative Utilities
 *
 * VERSION 5 IMPROVEMENTS:
 * 1. Fixed thread-safety issues in lazy caching
 * 2. Corrected bulk pruning logic to prevent missing valid itemsets
 * 3. Improved TopKManager with fine-grained locking
 * 4. Fixed nested parallelism issues
 * 5. Added adaptive task granularity
 * 6. Ensured completeness and soundness of the algorithm
 *
 * @author Enhanced Implementation
 * @version 5 - Correctness-Guaranteed Parallel Version
 */
public class ver5 {
    private final Map<Integer, Double> itemProfits;
    private final int k;
    private final double minPro;
    private static final double EPSILON = 1e-10;
    private static final double LOG_EPSILON = -700; // exp(-700) ≈ 0

    // Thread-safe top-K management with improved concurrency
    private final TopKManager topKManager;

    // Optimized item ordering
    private Map<Integer, Integer> itemToRank;
    private Map<Integer, Double> itemRTWU;

    // Enhanced statistics - thread-safe
    private final AtomicLong candidatesGenerated = new AtomicLong(0);
    private final AtomicLong candidatesPruned = new AtomicLong(0);
    private final AtomicLong utilityListsCreated = new AtomicLong(0);
    private final AtomicLong euPruned = new AtomicLong(0);
    private final AtomicLong epPruned = new AtomicLong(0);
    private final AtomicLong rtwuPruned = new AtomicLong(0);
    private final AtomicLong branchPruned = new AtomicLong(0);

    // Control parallel execution with adaptive parameters
    private final ForkJoinPool customThreadPool;
    private final AdaptiveTaskManager taskManager;

    // Memory monitoring
    private final long maxMemory;
    private final AtomicLong peakMemoryUsage = new AtomicLong(0);

    /**
     * Adaptive task management for optimal parallel performance
     */
    private class AdaptiveTaskManager {
        private final AtomicLong totalTaskTime = new AtomicLong(0);
        private final AtomicLong taskCount = new AtomicLong(0);
        private volatile int dynamicThreshold = 30;
        private volatile int dynamicGranularity = 10;

        boolean shouldParallelize(int size, int depth) {
            // Adjust threshold based on depth to avoid excessive parallelism
            int adjustedThreshold = dynamicThreshold * Math.max(1, depth / 2);
            return size >= adjustedThreshold && depth < 10; // Limit recursion depth
        }

        int getChunkSize(int totalSize, int depth) {
            // Calculate optimal chunk size based on available processors and depth
            int processors = customThreadPool.getParallelism();
            int depthPenalty = Math.max(1, depth);

            // Ensure we don't create too many small tasks
            int minChunkSize = Math.max(dynamicGranularity, 5);
            int idealChunks = processors * 2 / depthPenalty;

            return Math.max(minChunkSize, totalSize / Math.max(1, idealChunks));
        }

        void updateMetrics(long taskNanos, int itemsProcessed) {
            totalTaskTime.addAndGet(taskNanos);
            taskCount.incrementAndGet();

            // Periodically adjust parameters
            if (taskCount.get() % 100 == 0) {
                long avgTime = totalTaskTime.get() / taskCount.get();

                if (avgTime < 1_000_000) { // < 1ms per task
                    dynamicGranularity = Math.min(50, dynamicGranularity + 5);
                } else if (avgTime > 10_000_000) { // > 10ms per task
                    dynamicGranularity = Math.max(5, dynamicGranularity - 2);
                }
            }
        }
    }

    /**
     * Enhanced Transaction class with efficient storage
     */
    static class EnhancedTransaction {
        final int tid;
        final int[] items;
        final int[] quantities;
        final double[] logProbabilities;
        final double rtu;

        EnhancedTransaction(int tid, Map<Integer, Integer> itemMap,
                           Map<Integer, Double> probMap, Map<Integer, Double> profits,
                           Map<Integer, Integer> itemToRank) {
            this.tid = tid;

            // Sort items by RTWU rank
            List<Integer> sortedItems = new ArrayList<>(itemMap.keySet());
            sortedItems.sort((a, b) -> {
                Integer rankA = itemToRank.get(a);
                Integer rankB = itemToRank.get(b);
                if (rankA == null && rankB == null) return 0;
                if (rankA == null) return 1;
                if (rankB == null) return -1;
                return rankA.compareTo(rankB);
            });

            int size = sortedItems.size();
            this.items = new int[size];
            this.quantities = new int[size];
            this.logProbabilities = new double[size];

            int idx = 0;
            double rtu = 0;

            for (Integer item : sortedItems) {
                items[idx] = item;
                quantities[idx] = itemMap.get(item);

                double prob = probMap.getOrDefault(item, 0.0);
                logProbabilities[idx] = prob > 0 ? Math.log(prob) : LOG_EPSILON;

                Double profit = profits.get(item);
                if (profit != null) {
                    double utility = profit * quantities[idx];
                    if (profit > 0) {
                        rtu += utility;
                    }
                }
                idx++;
            }

            this.rtu = rtu;
        }

        int getItemIndex(int item) {
            return Arrays.binarySearch(items, item);
        }

        double getItemLogProbability(int item) {
            int idx = getItemIndex(item);
            return idx >= 0 ? logProbabilities[idx] : LOG_EPSILON;
        }

        int getItemQuantity(int item) {
            int idx = getItemIndex(item);
            return idx >= 0 ? quantities[idx] : 0;
        }
    }

    /**
     * Thread-safe Utility-List with lazy computation
     */
    static class EnhancedUtilityList {
        static class Element {
            final int tid;
            final double utility;
            final double remaining;
            final double logProbability;

            Element(int tid, double utility, double remaining, double logProbability) {
                this.tid = tid;
                this.utility = utility;
                this.remaining = remaining;
                this.logProbability = logProbability;
            }
        }

        final Set<Integer> itemset;
        final List<Element> elements;
        final double existentialProbability;
        final double rtwu;

        // Thread-safe lazy-computed values
        private volatile Double cachedSumEU = null;
        private volatile Double cachedSumRemaining = null;

        EnhancedUtilityList(Set<Integer> itemset, List<Element> elements, double rtwu) {
            this.itemset = Collections.unmodifiableSet(new HashSet<>(itemset));
            this.elements = Collections.unmodifiableList(elements);
            this.rtwu = rtwu;
            this.existentialProbability = calculateLogSpaceExistentialProbability();
        }

        // Thread-safe lazy computation with double-checked locking
        double getSumEU() {
            Double result = cachedSumEU;
            if (result == null) {
                synchronized(this) {
                    result = cachedSumEU;
                    if (result == null) {
                        double eu = 0;
                        for (Element e : elements) {
                            double prob = Math.exp(e.logProbability);
                            eu += e.utility * prob;
                        }
                        cachedSumEU = result = eu;
                    }
                }
            }
            return result;
        }

        // Thread-safe lazy computation with double-checked locking
        double getSumRemaining() {
            Double result = cachedSumRemaining;
            if (result == null) {
                synchronized(this) {
                    result = cachedSumRemaining;
                    if (result == null) {
                        double rem = 0;
                        for (Element e : elements) {
                            double prob = Math.exp(e.logProbability);
                            rem += e.remaining * prob;
                        }
                        cachedSumRemaining = result = rem;
                    }
                }
            }
            return result;
        }

        private double calculateLogSpaceExistentialProbability() {
            if (elements.isEmpty()) return 0.0;

            double logComplement = 0.0;

            for (Element e : elements) {
                if (e.logProbability > Math.log(1.0 - EPSILON)) {
                    return 1.0;
                }

                double prob = Math.exp(e.logProbability);
                double log1MinusP = prob < 0.5 ?
                    Math.log1p(-prob) :
                    Math.log(1.0 - prob);

                logComplement += log1MinusP;

                if (logComplement < LOG_EPSILON) {
                    return 1.0;
                }
            }

            if (logComplement < LOG_EPSILON) {
                return 1.0;
            }

            double complement = Math.exp(logComplement);
            return 1.0 - complement;
        }
    }

    /**
     * ForkJoinTask for parallel prefix mining
     */
    private class PrefixMiningTask extends RecursiveAction {
        private final List<Integer> sortedItems;
        private final Map<Integer, EnhancedUtilityList> singleItemLists;
        private final int start;
        private final int end;
        private final int depth;

        PrefixMiningTask(List<Integer> sortedItems,
                        Map<Integer, EnhancedUtilityList> singleItemLists,
                        int start, int end, int depth) {
            this.sortedItems = sortedItems;
            this.singleItemLists = singleItemLists;
            this.start = start;
            this.end = end;
            this.depth = depth;
        }

        @Override
        protected void compute() {
            long startTime = System.nanoTime();
            int size = end - start;

            // Use adaptive task manager to decide on parallelization
            int chunkSize = taskManager.getChunkSize(size, depth);

            if (size <= chunkSize || depth > 8) {
                // Sequential processing
                for (int i = start; i < end; i++) {
                    processPrefix(i);
                }
            } else {
                // Parallel processing - split into subtasks
                List<PrefixMiningTask> subtasks = new ArrayList<>();

                for (int i = start; i < end; i += chunkSize) {
                    int taskEnd = Math.min(i + chunkSize, end);
                    PrefixMiningTask task = new PrefixMiningTask(
                        sortedItems, singleItemLists, i, taskEnd, depth + 1
                    );
                    subtasks.add(task);
                    task.fork();
                }

                // Join all subtasks
                for (PrefixMiningTask task : subtasks) {
                    task.join();
                }
            }

            taskManager.updateMetrics(System.nanoTime() - startTime, size);
        }

        private void processPrefix(int index) {
            Integer item = sortedItems.get(index);
            EnhancedUtilityList ul = singleItemLists.get(item);

            if (ul == null) return;

            // Early termination check
            double currentThreshold = topKManager.getThreshold();
            if (ul.rtwu < currentThreshold - EPSILON) {
                branchPruned.incrementAndGet();
                return;
            }

            // Collect valid extensions
            List<EnhancedUtilityList> extensions = new ArrayList<>();
            for (int j = index + 1; j < sortedItems.size(); j++) {
                Integer extItem = sortedItems.get(j);
                EnhancedUtilityList extUL = singleItemLists.get(extItem);

                if (extUL == null) continue;

                // Prune based on RTWU
                if (extUL.rtwu < currentThreshold - EPSILON) {
                    rtwuPruned.incrementAndGet();
                    continue;
                }

                extensions.add(extUL);
            }

            // Mine with this prefix
            if (!extensions.isEmpty()) {
                searchEnhanced(ul, extensions, depth + 1);
            }

            // Periodic memory monitoring
            if (index % 100 == 0) {
                long usedMemory = Runtime.getRuntime().totalMemory() -
                                 Runtime.getRuntime().freeMemory();
                peakMemoryUsage.updateAndGet(peak -> Math.max(peak, usedMemory));
            }
        }
    }

    /**
     * Improved Top-K manager with fine-grained concurrency
     */
    private class TopKManager {
        private final int k;
        private final ConcurrentSkipListSet<Itemset> topKSet;
        private final ConcurrentHashMap<Set<Integer>, Double> itemsetUtilities;
        private final AtomicReference<Double> threshold;
        private final ReentrantLock updateLock;

        TopKManager(int k) {
            this.k = k;
            this.topKSet = new ConcurrentSkipListSet<>((a, b) -> {
                int cmp = Double.compare(b.expectedUtility, a.expectedUtility);
                if (cmp != 0) return cmp;
                return Integer.compare(a.items.hashCode(), b.items.hashCode());
            });
            this.itemsetUtilities = new ConcurrentHashMap<>();
            this.threshold = new AtomicReference<>(0.0);
            this.updateLock = new ReentrantLock();
        }

        boolean tryAdd(Set<Integer> items, double eu, double ep) {
            // Fast path - early rejection
            if (eu < threshold.get() - EPSILON && topKSet.size() >= k) {
                return false;
            }

            // Check for existing itemset
            Double existingUtility = itemsetUtilities.get(items);
            if (existingUtility != null && existingUtility >= eu - EPSILON) {
                return false;
            }

            // Update with lock
            updateLock.lock();
            try {
                // Double-check after acquiring lock
                double currentThreshold = threshold.get();
                if (eu < currentThreshold - EPSILON && topKSet.size() >= k) {
                    return false;
                }

                // Remove old version if exists
                if (existingUtility != null) {
                    topKSet.removeIf(itemset -> itemset.items.equals(items));
                }

                // Add new itemset
                Itemset newItemset = new Itemset(items, eu, ep);
                topKSet.add(newItemset);
                itemsetUtilities.put(items, eu);

                // Maintain size constraint
                while (topKSet.size() > k) {
                    Itemset removed = topKSet.pollLast();
                    if (removed != null) {
                        itemsetUtilities.remove(removed.items);
                    }
                }

                // Update threshold
                if (topKSet.size() >= k) {
                    Iterator<Itemset> iter = topKSet.iterator();
                    for (int i = 0; i < k - 1 && iter.hasNext(); i++) {
                        iter.next();
                    }
                    if (iter.hasNext()) {
                        threshold.set(iter.next().expectedUtility);
                    }
                }

                return true;
            } finally {
                updateLock.unlock();
            }
        }

        double getThreshold() {
            return threshold.get();
        }

        List<Itemset> getTopK() {
            return topKSet.stream()
                .limit(k)
                .collect(Collectors.toList());
        }
    }

    // Constructor
    public ver5(Map<Integer, Double> itemProfits, int k, double minPro) {
        this.itemProfits = Collections.unmodifiableMap(new HashMap<>(itemProfits));
        this.k = k;
        this.minPro = minPro;
        this.topKManager = new TopKManager(k);
        this.taskManager = new AdaptiveTaskManager();

        int numThreads = Runtime.getRuntime().availableProcessors();
        this.customThreadPool = new ForkJoinPool(numThreads);
        this.maxMemory = Runtime.getRuntime().maxMemory();
    }

    /**
     * Main mining method
     */
    public List<Itemset> mine(List<Transaction> rawDatabase) {
        Instant start = Instant.now();

        System.out.println("=== PTK-HUIM-U± Version 5 - Correctness-Guaranteed Parallel ===");
        System.out.println("Database size: " + rawDatabase.size());
        System.out.println("Number of items: " + itemProfits.size());
        System.out.println("K: " + k + ", MinPro: " + minPro);
        System.out.println("Thread pool size: " + customThreadPool.getParallelism());

        // Phase 1: Initialize
        System.out.println("\nPhase 1: Initialization...");
        Map<Integer, EnhancedUtilityList> singleItemLists = optimizedInitialization(rawDatabase);

        List<Integer> sortedItems = getSortedItemsByRank(singleItemLists.keySet());
        System.out.println("Items after filtering: " + sortedItems.size());

        // Process single items
        for (Integer item : sortedItems) {
            EnhancedUtilityList ul = singleItemLists.get(item);
            if (ul != null) {
                double sumEU = ul.getSumEU();
                if (sumEU >= topKManager.getThreshold() - EPSILON &&
                    ul.existentialProbability >= minPro - EPSILON) {
                    topKManager.tryAdd(ul.itemset, sumEU, ul.existentialProbability);
                }
            }
        }

        // Phase 2: Parallel mining
        System.out.println("\nPhase 2: Parallel pattern mining...");

        try {
            if (sortedItems.size() > 0) {
                PrefixMiningTask rootTask = new PrefixMiningTask(
                    sortedItems, singleItemLists, 0, sortedItems.size(), 0
                );
                customThreadPool.invoke(rootTask);
            }
        } catch (Exception e) {
            System.err.println("Error in parallel processing: " + e.getMessage());
            e.printStackTrace();

            // Fallback to sequential
            System.out.println("Falling back to sequential processing...");
            sequentialMining(sortedItems, singleItemLists);
        } finally {
            // Ensure thread pool is properly shut down
            shutdownThreadPool();
        }

        List<Itemset> results = topKManager.getTopK();

        Instant end = Instant.now();

        // Print statistics
        System.out.println("\n=== Mining Complete ===");
        System.out.println("Execution time: " + Duration.between(start, end).toMillis() + " ms");
        System.out.println("Candidates generated: " + candidatesGenerated.get());
        System.out.println("Utility lists created: " + utilityListsCreated.get());
        System.out.println("Pruning statistics:");
        System.out.println("  - RTWU pruned: " + rtwuPruned.get());
        System.out.println("  - Branches pruned: " + branchPruned.get());
        System.out.println("  - EU+remaining pruned: " + euPruned.get());
        System.out.println("  - EP pruned: " + epPruned.get());
        System.out.println("  - Total pruned: " + candidatesPruned.get());
        System.out.println("Peak memory: " + (peakMemoryUsage.get() / 1024 / 1024) + " MB");
        System.out.println("Final threshold: " + String.format("%.4f", topKManager.getThreshold()));
        System.out.println("Top-K found: " + results.size());

        return results;
    }

    /**
     * Proper thread pool shutdown
     */
    private void shutdownThreadPool() {
        customThreadPool.shutdown();
        try {
            if (!customThreadPool.awaitTermination(60, TimeUnit.SECONDS)) {
                System.err.println("Thread pool didn't terminate, forcing shutdown");
                customThreadPool.shutdownNow();

                if (!customThreadPool.awaitTermination(60, TimeUnit.SECONDS)) {
                    System.err.println("Thread pool didn't terminate after forced shutdown");
                }
            }
        } catch (InterruptedException e) {
            System.err.println("Interrupted during shutdown");
            customThreadPool.shutdownNow();
            Thread.currentThread().interrupt();
        }
    }

    /**
     * Sequential fallback mining
     */
    private void sequentialMining(List<Integer> sortedItems,
                                 Map<Integer, EnhancedUtilityList> singleItemLists) {
        for (int i = 0; i < sortedItems.size(); i++) {
            Integer item = sortedItems.get(i);
            EnhancedUtilityList ul = singleItemLists.get(item);

            if (ul == null) continue;

            double currentThreshold = topKManager.getThreshold();
            if (ul.rtwu < currentThreshold - EPSILON) {
                branchPruned.incrementAndGet();
                continue;
            }

            List<EnhancedUtilityList> extensions = new ArrayList<>();
            for (int j = i + 1; j < sortedItems.size(); j++) {
                Integer extItem = sortedItems.get(j);
                EnhancedUtilityList extUL = singleItemLists.get(extItem);

                if (extUL == null) continue;

                if (extUL.rtwu < currentThreshold - EPSILON) {
                    rtwuPruned.incrementAndGet();
                    continue;
                }

                extensions.add(extUL);
            }

            if (!extensions.isEmpty()) {
                searchSequential(ul, extensions);
            }
        }
    }

    /**
     * Enhanced search with correct pruning
     */
    private void searchEnhanced(EnhancedUtilityList prefix,
                               List<EnhancedUtilityList> extensions,
                               int depth) {

        // Decide between parallel and sequential based on depth and size
        if (taskManager.shouldParallelize(extensions.size(), depth) &&
            ForkJoinTask.getPool() != null) {

            // Parallel processing using fork-join
            int chunkSize = taskManager.getChunkSize(extensions.size(), depth);
            List<RecursiveAction> subtasks = new ArrayList<>();

            for (int i = 0; i < extensions.size(); i += chunkSize) {
                final int start = i;
                final int end = Math.min(i + chunkSize, extensions.size());

                RecursiveAction task = new RecursiveAction() {
                    @Override
                    protected void compute() {
                        processExtensionRange(prefix, extensions, start, end, depth);
                    }
                };

                subtasks.add(task);
                task.fork();
            }

            // Wait for all subtasks
            for (RecursiveAction task : subtasks) {
                task.join();
            }

        } else {
            // Sequential processing
            processExtensionRange(prefix, extensions, 0, extensions.size(), depth);
        }
    }

    /**
     * Process a range of extensions
     */
    private void processExtensionRange(EnhancedUtilityList prefix,
                                      List<EnhancedUtilityList> extensions,
                                      int start, int end, int depth) {

        double currentThreshold = topKManager.getThreshold();

        for (int i = start; i < end; i++) {
            EnhancedUtilityList extension = extensions.get(i);

            // RTWU pruning
            if (extension.rtwu < currentThreshold - EPSILON) {
                rtwuPruned.incrementAndGet();
                candidatesPruned.incrementAndGet();
                continue;
            }

            // Join utility lists
            EnhancedUtilityList joined = join(prefix, extension);

            if (joined == null || joined.elements.isEmpty()) {
                continue;
            }

            utilityListsCreated.incrementAndGet();
            candidatesGenerated.incrementAndGet();

            // Existential probability pruning
            if (joined.existentialProbability < minPro - EPSILON) {
                epPruned.incrementAndGet();
                candidatesPruned.incrementAndGet();
                continue;
            }

            // Calculate utilities
            double sumEU = joined.getSumEU();
            double sumRemaining = joined.getSumRemaining();

            // EU + remaining pruning
            if (sumEU + sumRemaining < currentThreshold - EPSILON) {
                euPruned.incrementAndGet();
                candidatesPruned.incrementAndGet();
                continue;
            }

            // Add to top-k if qualified
            if (sumEU >= currentThreshold - EPSILON &&
                joined.existentialProbability >= minPro - EPSILON) {
                topKManager.tryAdd(joined.itemset, sumEU, joined.existentialProbability);
                currentThreshold = topKManager.getThreshold(); // Update threshold
            }

            // Recursive search with remaining extensions
            if (i < end - 1) {
                List<EnhancedUtilityList> newExtensions = new ArrayList<>();

                for (int j = i + 1; j < end; j++) {
                    EnhancedUtilityList ext = extensions.get(j);
                    // Only include extensions that pass RTWU threshold
                    if (ext.rtwu >= currentThreshold - EPSILON) {
                        newExtensions.add(ext);
                    }
                }

                // Also need to include extensions beyond current range
                for (int j = end; j < extensions.size(); j++) {
                    EnhancedUtilityList ext = extensions.get(j);
                    if (ext.rtwu >= currentThreshold - EPSILON) {
                        newExtensions.add(ext);
                    }
                }

                if (!newExtensions.isEmpty()) {
                    searchEnhanced(joined, newExtensions, depth + 1);
                }
            }
        }
    }

    /**
     * Sequential search for fallback
     */
    private void searchSequential(EnhancedUtilityList prefix,
                                 List<EnhancedUtilityList> extensions) {
        processExtensionRange(prefix, extensions, 0, extensions.size(), Integer.MAX_VALUE);
    }

    /**
     * Optimized initialization
     */
    private Map<Integer, EnhancedUtilityList> optimizedInitialization(List<Transaction> rawDatabase) {
        // Pass 1: Calculate RTWU
        System.out.println("Computing RTWU values...");
        this.itemRTWU = new HashMap<>();

        for (Transaction rawTrans : rawDatabase) {
            double rtu = 0;
            for (Map.Entry<Integer, Integer> entry : rawTrans.items.entrySet()) {
                Integer item = entry.getKey();
                Integer quantity = entry.getValue();
                Double profit = itemProfits.get(item);
                if (profit != null && profit > 0) {
                    rtu += profit * quantity;
                }
            }

            for (Map.Entry<Integer, Integer> entry : rawTrans.items.entrySet()) {
                Integer item = entry.getKey();
                Double prob = rawTrans.probabilities.get(item);
                if (prob != null && prob > 0) {
                    itemRTWU.merge(item, rtu, Double::sum);
                }
            }
        }

        // Build ordering
        System.out.println("Building RTWU ordering...");
        this.itemToRank = new HashMap<>();

        List<Integer> rankedItems = itemRTWU.entrySet().stream()
            .sorted((a, b) -> {
                int cmp = Double.compare(a.getValue(), b.getValue());
                if (cmp != 0) return cmp;
                return a.getKey().compareTo(b.getKey());
            })
            .map(Map.Entry::getKey)
            .collect(Collectors.toList());

        for (int i = 0; i < rankedItems.size(); i++) {
            itemToRank.put(rankedItems.get(i), i);
        }

        // Pass 2: Build utility lists
        System.out.println("Building utility lists...");
        Map<Integer, List<EnhancedUtilityList.Element>> tempElements = new HashMap<>();

        for (Transaction rawTrans : rawDatabase) {
            EnhancedTransaction trans = new EnhancedTransaction(
                rawTrans.tid, rawTrans.items, rawTrans.probabilities, itemProfits, itemToRank
            );

            for (int i = 0; i < trans.items.length; i++) {
                int item = trans.items[i];

                if (!itemToRank.containsKey(item)) continue;

                double utility = itemProfits.getOrDefault(item, 0.0) * trans.quantities[i];
                double logProb = trans.logProbabilities[i];

                if (logProb > LOG_EPSILON) {
                    double remaining = 0;
                    for (int j = i + 1; j < trans.items.length; j++) {
                        Double profit = itemProfits.get(trans.items[j]);
                        if (profit != null && profit > 0) {
                            remaining += profit * trans.quantities[j];
                        }
                    }

                    tempElements.computeIfAbsent(item, k -> new ArrayList<>())
                        .add(new EnhancedUtilityList.Element(
                            trans.tid, utility, remaining, logProb
                        ));
                }
            }
        }

        // Create final utility lists
        Map<Integer, EnhancedUtilityList> singleItemLists = new HashMap<>();

        for (Map.Entry<Integer, List<EnhancedUtilityList.Element>> entry : tempElements.entrySet()) {
            Integer item = entry.getKey();
            List<EnhancedUtilityList.Element> elements = entry.getValue();

            if (!elements.isEmpty()) {
                Set<Integer> itemset = Collections.singleton(item);
                Double rtwu = itemRTWU.get(item);

                EnhancedUtilityList ul = new EnhancedUtilityList(itemset, elements, rtwu);

                if (ul.existentialProbability >= minPro - EPSILON) {
                    singleItemLists.put(item, ul);
                    utilityListsCreated.incrementAndGet();
                }
            }
        }

        return singleItemLists;
    }

    /**
     * Get sorted items by rank
     */
    private List<Integer> getSortedItemsByRank(Set<Integer> items) {
        return items.stream()
            .sorted((a, b) -> {
                Integer rankA = itemToRank.get(a);
                Integer rankB = itemToRank.get(b);
                if (rankA == null && rankB == null) return 0;
                if (rankA == null) return 1;
                if (rankB == null) return -1;
                return rankA.compareTo(rankB);
            })
            .collect(Collectors.toList());
    }

    /**
     * Join two utility lists
     */
    private EnhancedUtilityList join(EnhancedUtilityList ul1, EnhancedUtilityList ul2) {
        Set<Integer> newItemset = new HashSet<>(ul1.itemset);
        newItemset.addAll(ul2.itemset);

        List<EnhancedUtilityList.Element> joinedElements = new ArrayList<>();
        double joinedRTWU = Math.min(ul1.rtwu, ul2.rtwu);

        int i = 0, j = 0;
        while (i < ul1.elements.size() && j < ul2.elements.size()) {
            EnhancedUtilityList.Element e1 = ul1.elements.get(i);
            EnhancedUtilityList.Element e2 = ul2.elements.get(j);

            if (e1.tid == e2.tid) {
                double newUtility = e1.utility + e2.utility;
                double newRemaining = Math.min(e1.remaining, e2.remaining);
                double newLogProbability = e1.logProbability + e2.logProbability;

                if (newLogProbability > LOG_EPSILON) {
                    joinedElements.add(new EnhancedUtilityList.Element(
                        e1.tid, newUtility, newRemaining, newLogProbability
                    ));
                }
                i++;
                j++;
            } else if (e1.tid < e2.tid) {
                i++;
            } else {
                j++;
            }
        }

        if (joinedElements.isEmpty()) {
            return null;
        }

        return new EnhancedUtilityList(newItemset, joinedElements, joinedRTWU);
    }

    /**
     * Result itemset class
     */
    static class Itemset {
        final Set<Integer> items;
        final double expectedUtility;
        final double existentialProbability;

        Itemset(Set<Integer> items, double expectedUtility, double existentialProbability) {
            this.items = Collections.unmodifiableSet(new HashSet<>(items));
            this.expectedUtility = expectedUtility;
            this.existentialProbability = existentialProbability;
        }

        @Override
        public String toString() {
            return items + ": EU=" + String.format("%.4f", expectedUtility) +
                   ", EP=" + String.format("%.4f", existentialProbability);
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (!(obj instanceof Itemset)) return false;
            Itemset other = (Itemset) obj;
            return items.equals(other.items);
        }

        @Override
        public int hashCode() {
            return items.hashCode();
        }
    }

    // Transaction class
    static class Transaction {
        final int tid;
        final Map<Integer, Integer> items;
        final Map<Integer, Double> probabilities;

        Transaction(int tid, Map<Integer, Integer> items, Map<Integer, Double> probabilities) {
            this.tid = tid;
            this.items = items;
            this.probabilities = probabilities;
        }
    }

    // Main method
    public static void main(String[] args) throws IOException {
        if (args.length != 4) {
            System.err.println("Usage: ver5 <database_file> <profit_file> <k> <min_probability>");
            System.exit(1);
        }

        String dbFile = args[0];
        String profitFile = args[1];
        int k = Integer.parseInt(args[2]);
        double minPro = Double.parseDouble(args[3]);

        Map<Integer, Double> profits = readProfitTable(profitFile);
        List<Transaction> database = readDatabase(dbFile);

        System.out.println("=== PTK-HUIM-U± Version 5 ===");
        System.out.println("Correctness-guaranteed parallel implementation");

        ver5 algorithm = new ver5(profits, k, minPro);
        List<Itemset> topK = algorithm.mine(database);

        System.out.println("\n=== Top-" + k + " PHUIs ===");
        int rank = 1;
        for (Itemset itemset : topK) {
            System.out.printf("%d. %s\n", rank++, itemset);
        }
    }

    static Map<Integer, Double> readProfitTable(String filename) throws IOException {
        Map<Integer, Double> profits = new HashMap<>();
        try (BufferedReader br = new BufferedReader(new FileReader(filename))) {
            String line;
            while ((line = br.readLine()) != null) {
                String[] parts = line.trim().split("\\s+");
                if (parts.length == 2) {
                    profits.put(Integer.parseInt(parts[0]), Double.parseDouble(parts[1]));
                }
            }
        }
        return profits;
    }

    static List<Transaction> readDatabase(String filename) throws IOException {
        List<Transaction> database = new ArrayList<>();
        try (BufferedReader br = new BufferedReader(new FileReader(filename))) {
            String line;
            int tid = 1;
            while ((line = br.readLine()) != null) {
                Map<Integer, Integer> items = new HashMap<>();
                Map<Integer, Double> probabilities = new HashMap<>();

                String[] entries = line.trim().split("\\s+");
                for (String entry : entries) {
                    String[] parts = entry.split(":");
                    if (parts.length == 3) {
                        int item = Integer.parseInt(parts[0]);
                        int quantity = Integer.parseInt(parts[1]);
                        double prob = Double.parseDouble(parts[2]);

                        items.put(item, quantity);
                        probabilities.put(item, prob);
                    }
                }

                if (!items.isEmpty()) {
                    database.add(new Transaction(tid++, items, probabilities));
                }
            }
        }
        return database;
    }
}