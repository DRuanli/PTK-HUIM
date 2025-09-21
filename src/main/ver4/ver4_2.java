package main.ver4;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.stream.*;
import java.time.*;
import java.io.*;

/**
 * PTK-HUIM-U±: Enhanced Parallel Top-K High-Utility Itemset Mining
 * from Uncertain Databases with Positive and Negative Utilities
 *
 * VERSION 4_2 IMPROVEMENTS:
 * 1. Added EUCS (Estimated Utility Co-occurrence Structure) for tighter bounds
 * 2. Enhanced pre-join pruning using pairwise upper bounds
 * 3. Optimized memory usage with fallback mechanism
 * 4. Improved pruning statistics tracking
 *
 * @author Elio
 * @version 4.2
 */
public class ver4_2 {
    private final Map<Integer, Double> itemProfits;
    private final int k;
    private final double minPro;
    private static final double EPSILON = 1e-10;
    private static final double LOG_EPSILON = -700; // exp(-700) ≈ 0

    // Thread-safe top-K management
    private final TopKManager topKManager;

    // Optimized item ordering
    private Map<Integer, Integer> itemToRank;
    private Map<Integer, Double> itemRTWU;

    // EUCS structure for pairwise upper bounds
    private Map<Integer, Map<Integer, Double>> eucs;
    private static final int EUCS_MAX_ITEMS_THRESHOLD = 500; // Disable EUCS if too many items
    private boolean eucsEnabled = false;

    // Enhanced statistics - thread-safe
    private final AtomicLong candidatesGenerated = new AtomicLong(0);
    private final AtomicLong candidatesPruned = new AtomicLong(0);
    private final AtomicLong utilityListsCreated = new AtomicLong(0);
    private final AtomicLong euPruned = new AtomicLong(0);
    private final AtomicLong epPruned = new AtomicLong(0);
    private final AtomicLong rtwuPruned = new AtomicLong(0);
    private final AtomicLong eucsPruned = new AtomicLong(0); // New counter for EUCS pruning
    private final AtomicLong branchPruned = new AtomicLong(0);
    private final AtomicLong bulkBranchPruned = new AtomicLong(0);

    // Control parallel execution
    private final ForkJoinPool customThreadPool;
    private static final int PARALLEL_THRESHOLD = 30;
    private static final int TASK_GRANULARITY = 7;

    // Memory monitoring
    private final long maxMemory;
    private final AtomicLong peakMemoryUsage = new AtomicLong(0);

    /**
     * Enhanced Transaction class with efficient storage and RTWU ordering
     */
    static class EnhancedTransaction {
        final int tid;
        final int[] items;           // Sorted by RTWU order
        final int[] quantities;
        final double[] logProbabilities;
        final double rtu;            // Remaining Transaction Utility (positive only)

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

            // Convert to arrays for efficiency
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
     * Optimized Utility-List with on-demand calculation
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

        private Double cachedSumEU = null;
        private Double cachedSumRemaining = null;

        EnhancedUtilityList(Set<Integer> itemset, List<Element> elements, double rtwu) {
            this.itemset = Collections.unmodifiableSet(new HashSet<>(itemset));
            this.elements = Collections.unmodifiableList(elements);
            this.rtwu = rtwu;
            this.existentialProbability = calculateLogSpaceExistentialProbability();
        }

        double getSumEU() {
            if (cachedSumEU == null) {
                double eu = 0;
                for (Element e : elements) {
                    double prob = Math.exp(e.logProbability);
                    eu += e.utility * prob;
                }
                cachedSumEU = eu;
            }
            return cachedSumEU;
        }

        double getSumRemaining() {
            if (cachedSumRemaining == null) {
                double rem = 0;
                for (Element e : elements) {
                    double prob = Math.exp(e.logProbability);
                    rem += e.remaining * prob;
                }
                cachedSumRemaining = rem;
            }
            return cachedSumRemaining;
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

        PrefixMiningTask(List<Integer> sortedItems,
                         Map<Integer, EnhancedUtilityList> singleItemLists,
                         int start, int end) {
            this.sortedItems = sortedItems;
            this.singleItemLists = singleItemLists;
            this.start = start;
            this.end = end;
        }

        @Override
        protected void compute() {
            int size = end - start;

            if (size <= TASK_GRANULARITY) {
                for (int i = start; i < end; i++) {
                    processPrefix(i);
                }
            } else {
                int mid = start + (size / 2);
                PrefixMiningTask leftTask = new PrefixMiningTask(sortedItems, singleItemLists, start, mid);
                PrefixMiningTask rightTask = new PrefixMiningTask(sortedItems, singleItemLists, mid, end);

                leftTask.fork();
                rightTask.compute();
                leftTask.join();
            }
        }

        private void processPrefix(int index) {
            Integer item = sortedItems.get(index);
            EnhancedUtilityList ul = singleItemLists.get(item);

            if (ul == null) return;

            double currentThreshold = topKManager.getThreshold();
            if (itemRTWU.get(item) < currentThreshold - EPSILON) {
                branchPruned.incrementAndGet();
                return;
            }

            List<EnhancedUtilityList> extensions = new ArrayList<>();
            for (int j = index + 1; j < sortedItems.size(); j++) {
                Integer extItem = sortedItems.get(j);
                EnhancedUtilityList extUL = singleItemLists.get(extItem);

                if (extUL == null) continue;

                // EUCS pruning before RTWU check
                if (eucsEnabled && !checkEUCS(item, extItem, currentThreshold)) {
                    eucsPruned.incrementAndGet();
                    continue;
                }

                if (itemRTWU.get(extItem) < currentThreshold - EPSILON) {
                    rtwuPruned.incrementAndGet();
                    continue;
                }

                extensions.add(extUL);
            }

            if (!extensions.isEmpty()) {
                searchEnhanced(ul, extensions, singleItemLists);
            }

            if (index % 10 == 0) {
                long usedMemory = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory();
                peakMemoryUsage.updateAndGet(peak -> Math.max(peak, usedMemory));
            }
        }
    }

    /**
     * ForkJoinTask for parallel extension search
     */
    private class ExtensionSearchTask extends RecursiveAction {
        private final EnhancedUtilityList prefix;
        private final List<EnhancedUtilityList> extensions;
        private final Map<Integer, EnhancedUtilityList> singleItemLists;
        private final int start;
        private final int end;

        ExtensionSearchTask(EnhancedUtilityList prefix,
                        List<EnhancedUtilityList> extensions,
                        Map<Integer, EnhancedUtilityList> singleItemLists,
                        int start, int end) {
            this.prefix = prefix;
            this.extensions = extensions;
            this.singleItemLists = singleItemLists;
            this.start = start;
            this.end = end;
        }

        @Override
        protected void compute() {
            int size = end - start;

            if (size > 1) {
                double currentThreshold = topKManager.getThreshold();
                double minRTWU = Double.MAX_VALUE;
                for (int i = start; i < end; i++) {
                    EnhancedUtilityList ext = extensions.get(i);
                    if (ext.rtwu < minRTWU) {
                        minRTWU = ext.rtwu;
                    }
                }

                if (minRTWU < currentThreshold - EPSILON) {
                    bulkBranchPruned.incrementAndGet();
                    candidatesPruned.addAndGet(size);
                    return;
                }
            }

            if (size <= TASK_GRANULARITY) {
                for (int i = start; i < end; i++) {
                    processExtension(i);
                }
            } else {
                int mid = start + (size / 2);
                ExtensionSearchTask leftTask = new ExtensionSearchTask(
                    prefix, extensions, singleItemLists, start, mid
                );
                ExtensionSearchTask rightTask = new ExtensionSearchTask(
                    prefix, extensions, singleItemLists, mid, end
                );

                invokeAll(leftTask, rightTask);
            }
        }

        private void processExtension(int index) {
            EnhancedUtilityList extension = extensions.get(index);

            double currentThreshold = topKManager.getThreshold();

            // EUCS check for extension with prefix
            if (eucsEnabled) {
                Integer lastItem = getLastItemFromItemset(prefix.itemset);
                Integer extItem = extension.itemset.iterator().next();
                if (lastItem != null && extItem != null &&
                    !checkEUCS(lastItem, extItem, currentThreshold)) {
                    eucsPruned.incrementAndGet();
                    candidatesPruned.incrementAndGet();
                    return;
                }
            }

            if (extension.rtwu < currentThreshold - EPSILON) {
                rtwuPruned.incrementAndGet();
                candidatesPruned.incrementAndGet();
                return;
            }

            EnhancedUtilityList joined = ver4_2.this.join(prefix, extension);

            if (joined == null || joined.elements.isEmpty()) {
                return;
            }

            utilityListsCreated.incrementAndGet();
            candidatesGenerated.incrementAndGet();

            double threshold = topKManager.getThreshold();

            if (joined.existentialProbability < minPro - EPSILON) {
                epPruned.incrementAndGet();
                candidatesPruned.incrementAndGet();
                return;
            }

            double sumEU = joined.getSumEU();
            double sumRemaining = joined.getSumRemaining();

            if (sumEU + sumRemaining < threshold - EPSILON) {
                euPruned.incrementAndGet();
                candidatesPruned.incrementAndGet();
                return;
            }

            if (sumEU >= threshold - EPSILON &&
                joined.existentialProbability >= minPro - EPSILON) {
                topKManager.tryAdd(joined.itemset, sumEU, joined.existentialProbability);
            }

            if (index < extensions.size() - 1) {
                List<EnhancedUtilityList> newExtensions = new ArrayList<>();
                double currentThresholdForFilter = topKManager.getThreshold();

                for (int j = index + 1; j < extensions.size(); j++) {
                    EnhancedUtilityList ext = extensions.get(j);
                    if (ext.rtwu >= currentThresholdForFilter - EPSILON) {
                        newExtensions.add(ext);
                    } else {
                        rtwuPruned.incrementAndGet();
                    }
                }

                if (!newExtensions.isEmpty()) {
                    searchEnhanced(joined, newExtensions, singleItemLists);
                }
            }
        }
    }

    // ==================== MAIN ALGORITHM ====================

    public ver4_2(Map<Integer, Double> itemProfits, int k, double minPro) {
        this.itemProfits = Collections.unmodifiableMap(new HashMap<>(itemProfits));
        this.k = k;
        this.minPro = minPro;
        this.topKManager = new TopKManager(k);

        int numThreads = Runtime.getRuntime().availableProcessors();
        this.customThreadPool = new ForkJoinPool(numThreads);
        this.maxMemory = Runtime.getRuntime().maxMemory();
    }

    /**
     * Main mining method with EUCS enhancement
     */
    public List<Itemset> mine(List<Transaction> rawDatabase) {
        Instant start = Instant.now();

        System.out.println("=== Enhanced PTK-HUIM-U± v4.2 with EUCS ===");
        System.out.println("NEW: EUCS (Estimated Utility Co-occurrence Structure) for tighter bounds");
        System.out.println("Database size: " + rawDatabase.size());
        System.out.println("Number of items: " + itemProfits.size());
        System.out.println("K: " + k + ", MinPro: " + minPro);
        System.out.println("Available memory: " + (maxMemory / 1024 / 1024) + " MB");
        System.out.println("Thread pool size: " + customThreadPool.getParallelism());

        System.out.println("\nPhase 1: Initialization with EUCS building...");
        Map<Integer, EnhancedUtilityList> singleItemLists = optimizedInitialization(rawDatabase);

        List<Integer> sortedItems = getSortedItemsByRank(singleItemLists.keySet());
        System.out.println("Items after filtering: " + sortedItems.size());

        if (eucsEnabled) {
            System.out.println("EUCS enabled with " + countEUCSPairs() + " item pairs");
        } else {
            System.out.println("EUCS disabled (too many items or insufficient memory)");
        }

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

        System.out.println("\nPhase 2: Parallel mining with EUCS pruning...");

        if (sortedItems.size() >= PARALLEL_THRESHOLD) {
            System.out.println("Using parallel processing for " + sortedItems.size() + " items");
            try {
                PrefixMiningTask rootTask = new PrefixMiningTask(
                    sortedItems, singleItemLists, 0, sortedItems.size()
                );
                customThreadPool.invoke(rootTask);
            } catch (Exception e) {
                System.err.println("Error in parallel processing: " + e.getMessage());
                e.printStackTrace();
                sequentialMining(sortedItems, singleItemLists);
            }
        } else {
            System.out.println("Using sequential processing for " + sortedItems.size() + " items");
            sequentialMining(sortedItems, singleItemLists);
        }

        List<Itemset> results = topKManager.getTopK();

        Instant end = Instant.now();

        System.out.println("\n=== Mining Complete ===");
        System.out.println("Execution time: " + Duration.between(start, end).toMillis() + " ms");
        System.out.println("Candidates generated: " + candidatesGenerated.get());
        System.out.println("Utility lists created: " + utilityListsCreated.get());
        System.out.println("Enhanced pruning statistics:");
        System.out.println("  - EUCS pruned: " + eucsPruned.get());
        System.out.println("  - RTWU pruned: " + rtwuPruned.get());
        System.out.println("  - Branches pruned: " + branchPruned.get());
        System.out.println("  - Bulk branches pruned: " + bulkBranchPruned.get());
        System.out.println("  - EU+remaining pruned: " + euPruned.get());
        System.out.println("  - Existential probability pruned: " + epPruned.get());
        System.out.println("  - Total pruned: " + candidatesPruned.get());
        System.out.println("Peak memory usage: " + (peakMemoryUsage.get() / 1024 / 1024) + " MB");
        System.out.println("Final threshold: " + String.format("%.4f", topKManager.getThreshold()));
        System.out.println("Top-K found: " + results.size());

        customThreadPool.shutdown();
        try {
            if (!customThreadPool.awaitTermination(60, TimeUnit.SECONDS)) {
                System.err.println("Thread pool didn't terminate in 60 seconds, forcing shutdown");
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

        return results;
    }

    /**
     * Build EUCS structure for pairwise upper bounds
     */
    private void buildEUCS(List<Transaction> rawDatabase) {
        System.out.println("Building EUCS for pairwise upper-bounds...");
        this.eucs = new HashMap<>();

        for (Transaction rawTrans : rawDatabase) {
            // Create enhanced transaction with ordering
            EnhancedTransaction trans = new EnhancedTransaction(
                rawTrans.tid, rawTrans.items, rawTrans.probabilities, itemProfits, itemToRank
            );

            if (trans.items.length < 2) continue;

            double rtu = trans.rtu;

            // For each pair in transaction
            for (int p = 0; p < trans.items.length; p++) {
                int itemP = trans.items[p];
                if (trans.logProbabilities[p] <= LOG_EPSILON) continue;

                for (int q = p + 1; q < trans.items.length; q++) {
                    int itemQ = trans.items[q];
                    if (trans.logProbabilities[q] <= LOG_EPSILON) continue;

                    // Store with smaller item as first key for triangular matrix
                    int minItem = Math.min(itemP, itemQ);
                    int maxItem = Math.max(itemP, itemQ);

                    eucs.computeIfAbsent(minItem, k -> new HashMap<>())
                        .merge(maxItem, rtu, Double::sum);
                }
            }
        }

        eucsEnabled = true;
        System.out.println("EUCS built with " + countEUCSPairs() + " item pairs");
    }

    /**
     * Check EUCS bound for a pair of items
     */
    private boolean checkEUCS(Integer item1, Integer item2, double threshold) {
        if (!eucsEnabled || eucs == null) return true;

        int minItem = Math.min(item1, item2);
        int maxItem = Math.max(item1, item2);

        Map<Integer, Double> inner = eucs.get(minItem);
        if (inner == null) return true;

        Double pairBound = inner.get(maxItem);
        if (pairBound == null) return true;

        return pairBound >= threshold - EPSILON;
    }

    /**
     * Count number of pairs in EUCS
     */
    private int countEUCSPairs() {
        if (eucs == null) return 0;
        int count = 0;
        for (Map<Integer, Double> inner : eucs.values()) {
            count += inner.size();
        }
        return count;
    }

    /**
     * Get last item from itemset according to rank order
     */
    private Integer getLastItemFromItemset(Set<Integer> itemset) {
        return itemset.stream()
            .max(Comparator.comparingInt(item -> itemToRank.getOrDefault(item, Integer.MAX_VALUE)))
            .orElse(null);
    }

    /**
     * Sequential mining with EUCS
     */
    private void sequentialMining(List<Integer> sortedItems,
                              Map<Integer, EnhancedUtilityList> singleItemLists) {
        for (int i = 0; i < sortedItems.size(); i++) {
            Integer item = sortedItems.get(i);
            EnhancedUtilityList ul = singleItemLists.get(item);

            if (ul == null) continue;

            double currentThreshold = topKManager.getThreshold();
            if (itemRTWU.get(item) < currentThreshold - EPSILON) {
                branchPruned.incrementAndGet();
                continue;
            }

            List<EnhancedUtilityList> extensions = new ArrayList<>();
            for (int j = i + 1; j < sortedItems.size(); j++) {
                Integer extItem = sortedItems.get(j);
                EnhancedUtilityList extUL = singleItemLists.get(extItem);

                if (extUL == null) continue;

                // EUCS pruning
                if (eucsEnabled && !checkEUCS(item, extItem, currentThreshold)) {
                    eucsPruned.incrementAndGet();
                    continue;
                }

                if (itemRTWU.get(extItem) < currentThreshold - EPSILON) {
                    rtwuPruned.incrementAndGet();
                    continue;
                }

                extensions.add(extUL);
            }

            if (!extensions.isEmpty()) {
                searchEnhanced(ul, extensions, singleItemLists);
            }

            if (i % 10 == 0) {
                long usedMemory = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory();
                peakMemoryUsage.updateAndGet(peak -> Math.max(peak, usedMemory));
                System.out.println("Progress: " + (i + 1) + "/" + sortedItems.size() +
                                " items processed. Memory: " + (usedMemory / 1024 / 1024) + " MB" +
                                " EUCS pruned: " + eucsPruned.get());
            }
        }
    }

    /**
     * Optimized initialization with EUCS building
     */
    private Map<Integer, EnhancedUtilityList> optimizedInitialization(List<Transaction> rawDatabase) {
        // PASS 1: Calculate RTWU for each item
        System.out.println("Pass 1: Computing RTWU values...");
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

        // Build global ordering based on RTWU
        System.out.println("Building global RTWU ordering...");
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

        System.out.println("RTWU ordering established for " + itemToRank.size() + " items");

        // Check if EUCS should be enabled
        if (itemToRank.size() <= EUCS_MAX_ITEMS_THRESHOLD) {
            long estimatedEucsSize = (long) itemToRank.size() * itemToRank.size() / 2 * 16;
            if (estimatedEucsSize < maxMemory / 4) {
                buildEUCS(rawDatabase);
            } else {
                System.out.println("EUCS disabled due to memory constraints");
                eucsEnabled = false;
            }
        } else {
            System.out.println("EUCS disabled: too many items (" + itemToRank.size() + " > " + EUCS_MAX_ITEMS_THRESHOLD + ")");
            eucsEnabled = false;
        }

        // PASS 2: Build utility-lists
        System.out.println("Pass 2: Building utility-lists...");
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
     * Get items sorted by their rank
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
     * Search with EUCS-enhanced pruning
     */
    private void searchEnhanced(EnhancedUtilityList prefix, List<EnhancedUtilityList> extensions,
                           Map<Integer, EnhancedUtilityList> singleItemLists) {

        if (extensions.size() > 1) {
            double currentThreshold = topKManager.getThreshold();
            double minRTWU = Double.MAX_VALUE;
            for (EnhancedUtilityList ext : extensions) {
                if (ext.rtwu < minRTWU) {
                    minRTWU = ext.rtwu;
                }
            }

            if (minRTWU < currentThreshold - EPSILON) {
                bulkBranchPruned.incrementAndGet();
                candidatesPruned.addAndGet(extensions.size());
                return;
            }
        }

        if (extensions.size() >= PARALLEL_THRESHOLD && ForkJoinTask.inForkJoinPool()) {
            ExtensionSearchTask task = new ExtensionSearchTask(
                prefix, extensions, singleItemLists, 0, extensions.size()
            );
            task.invoke();
        } else {
            double currentThreshold = topKManager.getThreshold();

            for (int i = 0; i < extensions.size(); i++) {
                EnhancedUtilityList extension = extensions.get(i);

                // EUCS check
                if (eucsEnabled) {
                    Integer lastItem = getLastItemFromItemset(prefix.itemset);
                    Integer extItem = extension.itemset.iterator().next();
                    if (lastItem != null && extItem != null &&
                        !checkEUCS(lastItem, extItem, currentThreshold)) {
                        eucsPruned.incrementAndGet();
                        candidatesPruned.incrementAndGet();
                        continue;
                    }
                }

                if (extension.rtwu < currentThreshold - EPSILON) {
                    rtwuPruned.incrementAndGet();
                    candidatesPruned.incrementAndGet();
                    continue;
                }

                EnhancedUtilityList joined = join(prefix, extension);

                if (joined == null || joined.elements.isEmpty()) {
                    continue;
                }

                utilityListsCreated.incrementAndGet();
                candidatesGenerated.incrementAndGet();

                double threshold = topKManager.getThreshold();

                if (joined.existentialProbability < minPro - EPSILON) {
                    epPruned.incrementAndGet();
                    candidatesPruned.incrementAndGet();
                    continue;
                }

                double sumEU = joined.getSumEU();
                double sumRemaining = joined.getSumRemaining();

                if (sumEU + sumRemaining < threshold - EPSILON) {
                    euPruned.incrementAndGet();
                    candidatesPruned.incrementAndGet();
                    continue;
                }

                if (sumEU >= threshold - EPSILON &&
                    joined.existentialProbability >= minPro - EPSILON) {
                    topKManager.tryAdd(joined.itemset, sumEU, joined.existentialProbability);
                }

                if (i < extensions.size() - 1) {
                    List<EnhancedUtilityList> newExtensions = extensions.subList(i + 1, extensions.size());
                    searchEnhanced(joined, newExtensions, singleItemLists);
                }
            }
        }
    }

    /**
     * Join two utility-lists
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
     * Thread-safe top-K manager (unchanged from v4.1)
     */
    private class TopKManager {
        private final int k;
        private final ConcurrentSkipListSet<Itemset> topKSet;
        private final ConcurrentHashMap<Set<Integer>, Itemset> topKMap;
        private final AtomicReference<Double> threshold;
        private final Object lock = new Object();

        TopKManager(int k) {
            this.k = k;
            this.topKSet = new ConcurrentSkipListSet<>((a, b) -> {
                int cmp = Double.compare(b.expectedUtility, a.expectedUtility);
                if (cmp != 0) return cmp;
                return Integer.compare(a.hashCode(), b.hashCode());
            });
            this.topKMap = new ConcurrentHashMap<>();
            this.threshold = new AtomicReference<>(0.0);
        }

        boolean tryAdd(Set<Integer> items, double eu, double ep) {
            if (eu < threshold.get() - EPSILON) {
                return false;
            }

            Itemset existingItemset = topKMap.get(items);
            if (existingItemset != null && existingItemset.expectedUtility >= eu - EPSILON) {
                return false;
            }

            synchronized (lock) {
                if (topKSet.size() >= k && eu < threshold.get() - EPSILON) {
                    return false;
                }

                Itemset currentVersionInMap = topKMap.get(items);
                if (currentVersionInMap != null) {
                    if (currentVersionInMap.expectedUtility >= eu - EPSILON) {
                        return false;
                    }
                    topKSet.remove(currentVersionInMap);
                }

                Itemset newItemset = new Itemset(items, eu, ep);
                topKSet.add(newItemset);
                topKMap.put(items, newItemset);

                if (topKSet.size() > k) {
                    Itemset removed = topKSet.pollLast();
                    if (removed != null) {
                        topKMap.remove(removed.items);
                    }
                }

                if (topKSet.size() >= k) {
                    threshold.set(topKSet.last().expectedUtility);
                }
            }
            return true;
        }

        double getThreshold() {
            return threshold.get();
        }

        List<Itemset> getTopK() {
            return new ArrayList<>(topKSet);
        }
    }

    /**
     * Itemset result class
     */
    private static class Itemset {
        final Set<Integer> items;
        final double expectedUtility;
        final double probability;

        Itemset(Set<Integer> items, double eu, double p) {
            this.items = items;
            this.expectedUtility = eu;
            this.probability = p;
        }

        @Override
        public int hashCode() {
            return items.hashCode();
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (obj == null || getClass() != obj.getClass()) return false;
            Itemset other = (Itemset) obj;
            return items.equals(other.items);
        }

        @Override
        public String toString() {
            return "Itemset{" +
                    "items=" + items +
                    ", eu=" + String.format("%.2f", expectedUtility) +
                    '}';
        }
    }

    // ==================== ORIGINAL TRANSACTION CLASS ====================

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

    // ==================== MAIN METHOD ====================

    public static void main(String[] args) throws IOException {
        if (args.length != 4) {
            System.err.println("Usage: PTKHUIMEnhanced <database_file> <profit_file> <k> <min_probability>");
            System.exit(1);
        }

        String dbFile = args[0];
        String profitFile = args[1];
        int k = Integer.parseInt(args[2]);
        double minPro = Double.parseDouble(args[3]);

        Map<Integer, Double> profits = readProfitTable(profitFile);
        List<Transaction> database = readDatabase(dbFile);

        System.out.println("=== PTK-HUIM-U± Enhanced Version 4.2 ===");
        System.out.println("Key improvements:");
        System.out.println("1. EUCS (Estimated Utility Co-occurrence Structure)");
        System.out.println("2. Tighter pairwise upper bounds");
        System.out.println("3. Pre-join pruning optimization");
        System.out.println("4. Memory-aware fallback mechanism");
        System.out.println();

        ver4_2 algorithm = new ver4_2(profits, k, minPro);
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