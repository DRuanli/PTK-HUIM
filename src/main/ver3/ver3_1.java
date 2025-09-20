package main.ver3;

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
 * VERSION 2.1 IMPROVEMENTS:
 * 1. Enhanced thread safety with atomic operations
 * 2. Improved TopKManager synchronization
 * 3. Dynamic branch pruning based on RTWU
 * 4. Better thread pool management and shutdown
 * 5. Enhanced statistics tracking
 * 6. RTWU integration in utility lists
 * 7. Robust error handling
 * 8. Optimized configuration parameters
 *
 * EXCLUDED: EUCS and EUCP-based pruning for simplicity
 *
 * @author Enhanced Implementation
 * @version 3.1 - Thread Safety and Performance Optimizations
 */
public class ver3_1 {
    private final Map<Integer, Double> itemProfits;
    private final int k;
    private final double minPro;
    private static final double EPSILON = 1e-10;
    private static final double LOG_EPSILON = -700; // exp(-700) ≈ 0

    // Thread-safe top-K management
    private final TopKManager topKManager;

    // Transaction database (kept in memory after single scan)
    private List<EnhancedTransaction> database;

    // Item ordering based on RTWU (Redefined TWU for negative utilities)
    private Map<Integer, Integer> itemToRank;
    private Map<Integer, Double> itemRTWU;  // Store RTWU values for dynamic pruning
    private List<Integer> rankedItems;

    // Enhanced statistics - thread-safe
    private final AtomicLong candidatesGenerated = new AtomicLong(0);
    private final AtomicLong candidatesPruned = new AtomicLong(0);
    private final AtomicLong utilityListsCreated = new AtomicLong(0);
    private final AtomicLong euPruned = new AtomicLong(0);
    private final AtomicLong epPruned = new AtomicLong(0);
    private final AtomicLong rtwuPruned = new AtomicLong(0);
    private final AtomicLong branchPruned = new AtomicLong(0);

    // Control parallel execution - optimized parameters
    private final ForkJoinPool customThreadPool;
    private static final int PARALLEL_THRESHOLD = 30; // Increased for better efficiency
    private static final int TASK_GRANULARITY = 7;   // Optimized granularity

    // Memory monitoring - thread-safe
    private final long maxMemory;
    private final AtomicLong peakMemoryUsage = new AtomicLong(0);

    /**
     * Enhanced Transaction class with efficient storage and RTWU ordering
     */
    static class EnhancedTransaction {
        final int tid;
        final int[] items;           // Sorted by RTWU order
        final int[] quantities;
        final double[] logProbabilities;  // Store log probabilities to prevent underflow
        final double rtu;            // Remaining Transaction Utility (positive only)

        // Constructor for initial creation (before RTWU ordering is known)
        EnhancedTransaction(int tid, Map<Integer, Integer> itemMap,
                           Map<Integer, Double> probMap, Map<Integer, Double> profits) {
            this.tid = tid;

            // Convert to arrays for efficiency
            int size = itemMap.size();
            this.items = new int[size];
            this.quantities = new int[size];
            this.logProbabilities = new double[size];

            int idx = 0;
            double rtu = 0;

            // Temporarily store items (will be sorted by RTWU later)
            for (Map.Entry<Integer, Integer> entry : itemMap.entrySet()) {
                Integer item = entry.getKey();
                items[idx] = item;
                quantities[idx] = entry.getValue();

                // Store log probability
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

        // Constructor with RTWU ordering
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

                // Store log probability
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

        double getItemProbability(int item) {
            return Math.exp(getItemLogProbability(item));
        }

        int getItemQuantity(int item) {
            int idx = getItemIndex(item);
            return idx >= 0 ? quantities[idx] : 0;
        }

        boolean containsItem(int item) {
            return getItemIndex(item) >= 0;
        }
    }

    /**
     * Enhanced Utility-List with log-space probability tracking and RTWU integration
     */
    static class EnhancedUtilityList {
        static class Element {
            final int tid;
            final double utility;      // Actual utility in this transaction
            final double remaining;    // Remaining positive utility
            final double logProbability;  // Log probability for numerical stability

            Element(int tid, double utility, double remaining, double logProbability) {
                this.tid = tid;
                this.utility = utility;
                this.remaining = remaining;
                this.logProbability = logProbability;
            }

            double getProbability() {
                return Math.exp(logProbability);
            }
        }

        final Set<Integer> itemset;
        final List<Element> elements;
        final double sumEU;                    // Sum of expected utilities
        final double sumRemaining;             // Upper bound for extensions
        final double existentialProbability;   // Correctly calculated EP
        final double rtwu;                     // RTWU value for this itemset

        EnhancedUtilityList(Set<Integer> itemset) {
            this.itemset = Collections.unmodifiableSet(new HashSet<>(itemset));
            this.elements = new ArrayList<>();
            this.rtwu = 0.0;
            this.sumEU = 0;
            this.sumRemaining = 0;
            this.existentialProbability = 0;
        }

        EnhancedUtilityList(Set<Integer> itemset, List<Element> elements, double rtwu) {
            this.itemset = Collections.unmodifiableSet(new HashSet<>(itemset));
            this.elements = Collections.unmodifiableList(elements);
            this.rtwu = rtwu;

            // Calculate aggregates
            double eu = 0, rem = 0;

            for (Element e : elements) {
                double prob = Math.exp(e.logProbability);
                eu += e.utility * prob;  // Expected utility
                rem += e.remaining * prob; // Expected remaining
            }

            this.sumEU = eu;
            this.sumRemaining = rem;

            // Calculate existential probability in log-space
            this.existentialProbability = calculateLogSpaceExistentialProbability();
        }

        /**
         * Calculate existential probability using log-space for numerical stability
         * EP(X) = 1 - ∏(T∈D, X⊆T) [1 - P(X,T)]
         */
        private double calculateLogSpaceExistentialProbability() {
            if (elements.isEmpty()) return 0.0;

            // Sum of log(1 - P(X,T)) for all transactions
            double logComplement = 0.0;

            for (Element e : elements) {
                if (e.logProbability > Math.log(1.0 - EPSILON)) {
                    // Probability is essentially 1
                    return 1.0;
                }

                // Compute log(1 - P) stably using log1p
                double prob = Math.exp(e.logProbability);
                double log1MinusP = prob < 0.5 ?
                    Math.log1p(-prob) :
                    Math.log(1.0 - prob);

                logComplement += log1MinusP;

                // Early termination if product becomes too small
                if (logComplement < LOG_EPSILON) {
                    return 1.0;
                }
            }

            // Convert back: EP = 1 - exp(logComplement)
            if (logComplement < LOG_EPSILON) {
                return 1.0;
            }

            double complement = Math.exp(logComplement);
            return 1.0 - complement;
        }
    }

    /**
     * ForkJoinTask for parallel prefix mining with dynamic pruning
     */
    private class PrefixMiningTask extends RecursiveAction {
        private final List<Map.Entry<Integer, EnhancedUtilityList>> prefixes;
        private final Map<Integer, EnhancedUtilityList> singleItemLists;
        private final int start;
        private final int end;

        PrefixMiningTask(List<Map.Entry<Integer, EnhancedUtilityList>> prefixes,
                         Map<Integer, EnhancedUtilityList> singleItemLists,
                         int start, int end) {
            this.prefixes = prefixes;
            this.singleItemLists = singleItemLists;
            this.start = start;
            this.end = end;
        }

        @Override
        protected void compute() {
            int size = end - start;

            // Base case: process sequentially if small enough
            if (size <= TASK_GRANULARITY) {
                for (int i = start; i < end; i++) {
                    processPrefix(i);
                }
            } else {
                // Divide and conquer
                int mid = start + (size / 2);
                PrefixMiningTask leftTask = new PrefixMiningTask(prefixes, singleItemLists, start, mid);
                PrefixMiningTask rightTask = new PrefixMiningTask(prefixes, singleItemLists, mid, end);

                // Fork left task and compute right task in current thread
                leftTask.fork();
                rightTask.compute();
                leftTask.join();
            }
        }

        private void processPrefix(int index) {
            Integer item = prefixes.get(index).getKey();
            EnhancedUtilityList ul = prefixes.get(index).getValue();

            // Dynamic branch pruning based on RTWU
            double currentThreshold = topKManager.getThreshold();
            if (itemRTWU.get(item) < currentThreshold - EPSILON) {
                branchPruned.incrementAndGet();
                return;
            }

            // Get extensions with RTWU-based filtering
            List<EnhancedUtilityList> extensions = new ArrayList<>();
            for (int j = index + 1; j < prefixes.size(); j++) {
                Integer extItem = prefixes.get(j).getKey();

                // Skip if extension's RTWU is too low
                if (itemRTWU.get(extItem) < currentThreshold - EPSILON) {
                    rtwuPruned.incrementAndGet();
                    continue;
                }

                extensions.add(prefixes.get(j).getValue());
            }

            // Mine with this prefix
            if (!extensions.isEmpty()) {
                searchEnhanced(ul, extensions, singleItemLists);
            }

            // Monitor memory usage periodically - thread-safe
            if (index % 10 == 0) {
                long usedMemory = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory();
                peakMemoryUsage.updateAndGet(peak -> Math.max(peak, usedMemory));
            }
        }
    }

    /**
     * ForkJoinTask for parallel extension search with enhanced pruning
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

            // Process sequentially if small
            if (size <= TASK_GRANULARITY) {
                for (int i = start; i < end; i++) {
                    processExtension(i);
                }
            } else {
                // Split the work
                int mid = start + (size / 2);
                ExtensionSearchTask leftTask = new ExtensionSearchTask(
                    prefix, extensions, singleItemLists, start, mid
                );
                ExtensionSearchTask rightTask = new ExtensionSearchTask(
                    prefix, extensions, singleItemLists, mid, end
                );

                // Execute in parallel
                invokeAll(leftTask, rightTask);
            }
        }

        private void processExtension(int index) {
            EnhancedUtilityList extension = extensions.get(index);

            // Dynamic RTWU pruning
            double currentThreshold = topKManager.getThreshold();
            if (extension.rtwu < currentThreshold - EPSILON) {
                rtwuPruned.incrementAndGet();
                candidatesPruned.incrementAndGet();
                return;
            }

            // Join to create new utility-list
            EnhancedUtilityList joined = ver3_1.this.join(prefix, extension);

            if (joined == null || joined.elements.isEmpty()) {
                return;
            }

            utilityListsCreated.incrementAndGet();
            candidatesGenerated.incrementAndGet();

            double threshold = topKManager.getThreshold();

            // Pruning Strategy 1: Existential probability
            if (joined.existentialProbability < minPro - EPSILON) {
                epPruned.incrementAndGet();
                candidatesPruned.incrementAndGet();
                return;
            }

            // Pruning Strategy 2: EU + remaining
            if (joined.sumEU + joined.sumRemaining < threshold - EPSILON) {
                euPruned.incrementAndGet();
                candidatesPruned.incrementAndGet();
                return;
            }

            // Update top-k if qualified
            if (joined.sumEU >= threshold - EPSILON &&
                joined.existentialProbability >= minPro - EPSILON) {
                topKManager.tryAdd(joined.itemset, joined.sumEU, joined.existentialProbability);
            }

            // Recursive search with RTWU-filtered extensions
            if (index < extensions.size() - 1) {
                List<EnhancedUtilityList> newExtensions = new ArrayList<>();
                for (int j = index + 1; j < extensions.size(); j++) {
                    EnhancedUtilityList ext = extensions.get(j);

                    // Filter based on RTWU
                    if (ext.rtwu >= currentThreshold - EPSILON) {
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

    public ver3_1(Map<Integer, Double> itemProfits, int k, double minPro) {
        this.itemProfits = Collections.unmodifiableMap(new HashMap<>(itemProfits));
        this.k = k;
        this.minPro = minPro;
        this.topKManager = new TopKManager(k);

        int numThreads = Runtime.getRuntime().availableProcessors();
        this.customThreadPool = new ForkJoinPool(numThreads);

        this.maxMemory = Runtime.getRuntime().maxMemory();
    }

    /**
     * Main mining method with enhanced parallel processing and dynamic pruning
     */
    public List<Itemset> mine(List<Transaction> rawDatabase) {
        Instant start = Instant.now();

        System.out.println("=== Enhanced PTK-HUIM-U± v2.1 ===");
        System.out.println("Improvements: Thread Safety, Dynamic Pruning, Better Thread Management");
        System.out.println("Database size: " + rawDatabase.size());
        System.out.println("Number of items: " + itemProfits.size());
        System.out.println("K: " + k + ", MinPro: " + minPro);
        System.out.println("Available memory: " + (maxMemory / 1024 / 1024) + " MB");
        System.out.println("Thread pool size: " + customThreadPool.getParallelism());

        // Two-pass initialization with enhanced RTWU tracking
        System.out.println("\nPhase 1: Two-pass initialization with RTWU tracking...");
        Map<Integer, EnhancedUtilityList> singleItemLists = twoPassInitialization(rawDatabase);

        // Sort items by RTWU for effective pruning
        List<Map.Entry<Integer, EnhancedUtilityList>> sortedItems = sortItemsByRTWU(singleItemLists);

        System.out.println("Items after filtering: " + sortedItems.size());

        // Process single items
        for (Map.Entry<Integer, EnhancedUtilityList> entry : sortedItems) {
            EnhancedUtilityList ul = entry.getValue();
            if (ul.sumEU >= topKManager.getThreshold() - EPSILON &&
                ul.existentialProbability >= minPro - EPSILON) {
                topKManager.tryAdd(ul.itemset, ul.sumEU, ul.existentialProbability);
            }
        }

        System.out.println("\nPhase 2: Enhanced parallel mining with dynamic pruning...");

        // Use ForkJoinPool for parallel mining with improved management
        if (sortedItems.size() >= PARALLEL_THRESHOLD) {
            System.out.println("Using parallel processing for " + sortedItems.size() + " items");

            try {
                // Direct invocation for better thread pool utilization
                PrefixMiningTask rootTask = new PrefixMiningTask(
                    sortedItems, singleItemLists, 0, sortedItems.size()
                );
                customThreadPool.invoke(rootTask);

            } catch (Exception e) {
                System.err.println("Error in parallel processing: " + e.getMessage());
                e.printStackTrace();
                // Fall back to sequential processing
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
        System.out.println("  - RTWU pruned: " + rtwuPruned.get());
        System.out.println("  - Branches pruned: " + branchPruned.get());
        System.out.println("  - EU+remaining pruned: " + euPruned.get());
        System.out.println("  - Existential probability pruned: " + epPruned.get());
        System.out.println("  - Total pruned: " + candidatesPruned.get());
        System.out.println("Peak memory usage: " + (peakMemoryUsage.get() / 1024 / 1024) + " MB");
        System.out.println("Final threshold: " + String.format("%.4f", topKManager.getThreshold()));
        System.out.println("Top-K found: " + results.size());

        // Enhanced thread pool shutdown with proper timeout
        customThreadPool.shutdown();
        try {
            // Wait up to 60 seconds for normal termination
            if (!customThreadPool.awaitTermination(60, TimeUnit.SECONDS)) {
                System.err.println("Thread pool didn't terminate in 60 seconds, forcing shutdown");
                customThreadPool.shutdownNow();

                // Wait another 60 seconds for forced termination
                if (!customThreadPool.awaitTermination(60, TimeUnit.SECONDS)) {
                    System.err.println("Thread pool didn't terminate after forced shutdown");
                }
            }
        } catch (InterruptedException e) {
            System.err.println("Interrupted during shutdown");
            customThreadPool.shutdownNow();
            Thread.currentThread().interrupt();  // Preserve interrupt status
        }

        return results;
    }

    /**
     * Sequential mining with dynamic pruning
     */
    private void sequentialMining(List<Map.Entry<Integer, EnhancedUtilityList>> sortedItems,
                                  Map<Integer, EnhancedUtilityList> singleItemLists) {
        for (int i = 0; i < sortedItems.size(); i++) {
            Integer item = sortedItems.get(i).getKey();
            EnhancedUtilityList ul = sortedItems.get(i).getValue();

            // Dynamic branch pruning
            double currentThreshold = topKManager.getThreshold();
            if (itemRTWU.get(item) < currentThreshold - EPSILON) {
                branchPruned.incrementAndGet();
                continue;
            }

            // Get extensions with RTWU filtering
            List<EnhancedUtilityList> extensions = new ArrayList<>();
            for (int j = i + 1; j < sortedItems.size(); j++) {
                Integer extItem = sortedItems.get(j).getKey();

                // Skip if extension's RTWU is too low
                if (itemRTWU.get(extItem) < currentThreshold - EPSILON) {
                    rtwuPruned.incrementAndGet();
                    continue;
                }

                extensions.add(sortedItems.get(j).getValue());
            }

            // Mine with this prefix
            if (!extensions.isEmpty()) {
                searchEnhanced(ul, extensions, singleItemLists);
            }

            // Monitor memory usage - thread-safe
            if (i % 10 == 0) {
                long usedMemory = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory();
                peakMemoryUsage.updateAndGet(peak -> Math.max(peak, usedMemory));
                System.out.println("Progress: " + (i + 1) + "/" + sortedItems.size() +
                                 " items processed. Memory used: " + (usedMemory / 1024 / 1024) + " MB");
            }
        }
    }

    /**
     * Two-pass initialization with enhanced RTWU tracking
     */
    private Map<Integer, EnhancedUtilityList> twoPassInitialization(List<Transaction> rawDatabase) {
        // PASS 1: Calculate RTWU for each item
        System.out.println("Pass 1: Computing RTWU values...");
        this.itemRTWU = new HashMap<>();
        Map<Integer, Double> itemProb = new HashMap<>();

        for (Transaction rawTrans : rawDatabase) {
            // Calculate RTU for this transaction (only positive utilities)
            double rtu = 0;
            for (Map.Entry<Integer, Integer> entry : rawTrans.items.entrySet()) {
                Integer item = entry.getKey();
                Integer quantity = entry.getValue();
                Double profit = itemProfits.get(item);
                if (profit != null && profit > 0) {
                    rtu += profit * quantity;
                }
            }

            // Add RTU to RTWU of each item in transaction
            for (Map.Entry<Integer, Integer> entry : rawTrans.items.entrySet()) {
                Integer item = entry.getKey();
                Double prob = rawTrans.probabilities.get(item);
                if (prob != null && prob > 0) {
                    itemRTWU.merge(item, rtu, Double::sum);
                    itemProb.merge(item, prob, Double::sum);
                }
            }
        }

        // Build global ordering based on RTWU
        System.out.println("Building global RTWU ordering...");
        this.itemToRank = new HashMap<>();
        this.rankedItems = itemRTWU.entrySet().stream()
            .sorted((a, b) -> {
                int cmp = Double.compare(a.getValue(), b.getValue());
                if (cmp != 0) return cmp;
                return a.getKey().compareTo(b.getKey()); // Tie-break on item-id
            })
            .map(Map.Entry::getKey)
            .collect(Collectors.toList());

        for (int i = 0; i < rankedItems.size(); i++) {
            itemToRank.put(rankedItems.get(i), i);
        }

        System.out.println("RTWU ordering established for " + itemToRank.size() + " items");

        // PASS 2: Build database with RTWU-ordered transactions and utility-lists
        System.out.println("Pass 2: Building RTWU-ordered database and utility-lists...");
        this.database = new ArrayList<>();
        Map<Integer, List<TempElement>> itemTempElements = new HashMap<>();

        int processedCount = 0;
        for (Transaction rawTrans : rawDatabase) {
            // Create enhanced transaction with RTWU ordering
            EnhancedTransaction trans = new EnhancedTransaction(
                rawTrans.tid, rawTrans.items, rawTrans.probabilities, itemProfits, itemToRank
            );
            database.add(trans);

            // Build temporary elements for each item
            for (int i = 0; i < trans.items.length; i++) {
                int item = trans.items[i];

                // Only process items that have been assigned a rank
                if (!itemToRank.containsKey(item)) continue;

                double utility = itemProfits.getOrDefault(item, 0.0) * trans.quantities[i];
                double logProb = trans.logProbabilities[i];

                // Only process items with non-negligible probability
                if (logProb > LOG_EPSILON) {
                    itemTempElements.computeIfAbsent(item, k -> new ArrayList<>())
                        .add(new TempElement(trans.tid, utility, logProb, i, trans));
                }
            }

            // Progress reporting
            if (++processedCount % 10000 == 0) {
                System.out.println("Processed " + processedCount + " transactions...");
            }
        }

        // Build proper utility-lists
        Map<Integer, EnhancedUtilityList> singleItemLists = new HashMap<>();

        for (Map.Entry<Integer, List<TempElement>> entry : itemTempElements.entrySet()) {
            Integer item = entry.getKey();
            List<TempElement> tempElements = entry.getValue();

            // Check if item probability meets threshold
            Double totalProb = itemProb.get(item);
            if (totalProb == null || totalProb < minPro) {
                continue;
            }

            // Build proper elements with correct remaining utility
            List<EnhancedUtilityList.Element> elements = new ArrayList<>();
            for (TempElement temp : tempElements) {
                double remaining = calculateRemainingUtilityForElement(
                    temp.trans, temp.position, itemToRank
                );

                elements.add(new EnhancedUtilityList.Element(
                    temp.tid, temp.utility, remaining, temp.logProb
                ));
            }

            if (!elements.isEmpty()) {
                Set<Integer> itemset = Collections.singleton(item);
                Double rtwu = itemRTWU.get(item);

                // Create utility list with RTWU integration
                EnhancedUtilityList ul = new EnhancedUtilityList(itemset, elements, rtwu);

                // Only keep if passes basic filters
                if (ul.existentialProbability >= minPro - EPSILON) {
                    singleItemLists.put(item, ul);
                    utilityListsCreated.incrementAndGet();
                }
            }
        }

        // Clear temporary structures to free memory
        itemTempElements.clear();
        itemProb.clear();

        System.out.println("Single item utility-lists created: " + singleItemLists.size());

        System.gc(); // Suggest garbage collection after initialization

        return singleItemLists;
    }

    /**
     * Temporary element for two-phase processing
     */
    private static class TempElement {
        final int tid;
        final double utility;
        final double logProb;
        final int position;
        final EnhancedTransaction trans;

        TempElement(int tid, double utility, double logProb, int position, EnhancedTransaction trans) {
            this.tid = tid;
            this.utility = utility;
            this.logProb = logProb;
            this.position = position;
            this.trans = trans;
        }
    }

    /**
     * Calculate remaining utility for a specific element
     */
    private double calculateRemainingUtilityForElement(EnhancedTransaction trans, int position,
                                                       Map<Integer, Integer> itemRank) {
        double remaining = 0;
        int currentItem = trans.items[position];
        Integer currentRank = itemRank.get(currentItem);

        if (currentRank == null) return 0;

        // Items are now ordered by RTWU, so we only need to look at items after position
        for (int i = position + 1; i < trans.items.length; i++) {
            int item = trans.items[i];
            Integer itemRankVal = itemRank.get(item);

            // Since transaction is RTWU-ordered, items after position have higher RTWU
            if (itemRankVal != null && itemRankVal > currentRank) {
                Double profit = itemProfits.get(item);
                if (profit != null && profit > 0) {
                    remaining += profit * trans.quantities[i];
                }
            }
        }

        return remaining;
    }

    /**
     * Sort items by RTWU
     */
    private List<Map.Entry<Integer, EnhancedUtilityList>> sortItemsByRTWU(
            Map<Integer, EnhancedUtilityList> singleItemLists) {

        return singleItemLists.entrySet().stream()
            .sorted((a, b) -> {
                // Use the pre-computed RTWU ranking
                Integer rankA = itemToRank.get(a.getKey());
                Integer rankB = itemToRank.get(b.getKey());
                if (rankA == null && rankB == null) return 0;
                if (rankA == null) return 1;
                if (rankB == null) return -1;
                return rankA.compareTo(rankB);
            })
            .collect(Collectors.toList());
    }

    /**
     * Search with enhanced pruning strategies and parallel execution
     */
    private void searchEnhanced(EnhancedUtilityList prefix, List<EnhancedUtilityList> extensions,
                               Map<Integer, EnhancedUtilityList> singleItemLists) {

        // Decide whether to parallelize based on extension count
        if (extensions.size() >= PARALLEL_THRESHOLD && ForkJoinTask.inForkJoinPool()) {
            // Use parallel processing for large extension sets
            ExtensionSearchTask task = new ExtensionSearchTask(
                prefix, extensions, singleItemLists, 0, extensions.size()
            );
            task.invoke();
        } else {
            // Sequential processing for small extension sets
            double currentThreshold = topKManager.getThreshold();

            for (int i = 0; i < extensions.size(); i++) {
                EnhancedUtilityList extension = extensions.get(i);

                // Dynamic RTWU pruning
                if (extension.rtwu < currentThreshold - EPSILON) {
                    rtwuPruned.incrementAndGet();
                    candidatesPruned.incrementAndGet();
                    continue;
                }

                // Join to create new utility-list
                EnhancedUtilityList joined = join(prefix, extension);

                if (joined == null || joined.elements.isEmpty()) {
                    continue;
                }

                utilityListsCreated.incrementAndGet();
                candidatesGenerated.incrementAndGet();

                double threshold = topKManager.getThreshold();

                // Pruning Strategy 1: Existential probability (mathematically sound)
                if (joined.existentialProbability < minPro - EPSILON) {
                    epPruned.incrementAndGet();
                    candidatesPruned.incrementAndGet();
                    continue;
                }

                // Pruning Strategy 2: EU + remaining (mathematically sound)
                if (joined.sumEU + joined.sumRemaining < threshold - EPSILON) {
                    euPruned.incrementAndGet();
                    candidatesPruned.incrementAndGet();
                    continue;
                }

                // Update top-k if qualified
                if (joined.sumEU >= threshold - EPSILON &&
                    joined.existentialProbability >= minPro - EPSILON) {
                    topKManager.tryAdd(joined.itemset, joined.sumEU, joined.existentialProbability);
                }

                // Recursive search
                if (i < extensions.size() - 1) {
                    List<EnhancedUtilityList> newExtensions = extensions.subList(i + 1, extensions.size());
                    searchEnhanced(joined, newExtensions, singleItemLists);
                }
            }
        }
    }

    /**
     * Join two utility-lists with log-space probability handling and RTWU tracking
     */
    private EnhancedUtilityList join(EnhancedUtilityList ul1, EnhancedUtilityList ul2) {
        Set<Integer> newItemset = new HashSet<>(ul1.itemset);
        newItemset.addAll(ul2.itemset);

        List<EnhancedUtilityList.Element> joinedElements = new ArrayList<>();

        // Calculate joined RTWU (minimum of the two)
        double joinedRTWU = Math.min(ul1.rtwu, ul2.rtwu);

        int i = 0, j = 0;
        while (i < ul1.elements.size() && j < ul2.elements.size()) {
            EnhancedUtilityList.Element e1 = ul1.elements.get(i);
            EnhancedUtilityList.Element e2 = ul2.elements.get(j);

            if (e1.tid == e2.tid) {
                double newUtility = e1.utility + e2.utility;
                double newRemaining = Math.min(e1.remaining, e2.remaining);

                // Multiply probabilities in log-space
                double newLogProbability = e1.logProbability + e2.logProbability;

                // Only add if probability is significant
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
     * Enhanced thread-safe top-K manager with proper synchronization
     */
    private class TopKManager {
        private final int k;
        private final ConcurrentSkipListSet<Itemset> topKSet;
        private final ConcurrentHashMap<Set<Integer>, Itemset> itemsetMap;
        private final AtomicReference<Double> threshold;
        private final Object lock = new Object();  // Explicit lock for consistency

        TopKManager(int k) {
            this.k = k;
            this.topKSet = new ConcurrentSkipListSet<>((a, b) -> {
                int cmp = Double.compare(b.expectedUtility, a.expectedUtility);
                if (cmp != 0) return cmp;
                return Integer.compare(a.items.hashCode(), b.items.hashCode());
            });
            this.itemsetMap = new ConcurrentHashMap<>();
            this.threshold = new AtomicReference<>(0.0);
        }

        boolean tryAdd(Set<Integer> items, double eu, double ep) {
            double currentThreshold = threshold.get();

            if (eu < currentThreshold - EPSILON && topKSet.size() >= k) {
                return false;
            }

            Itemset newItemset = new Itemset(items, eu, ep);

            synchronized (lock) {  // Synchronize entire critical section
                Itemset existing = itemsetMap.get(items);

                if (existing != null) {
                    if (existing.expectedUtility < eu - EPSILON) {
                        topKSet.remove(existing);
                        topKSet.add(newItemset);
                        itemsetMap.put(items, newItemset);
                        updateThresholdLocked();
                        return true;
                    }
                    return false;
                }

                // Add new itemset
                itemsetMap.put(items, newItemset);
                topKSet.add(newItemset);

                // Remove excess if needed
                if (topKSet.size() > k) {
                    Itemset removed = topKSet.pollLast();
                    if (removed != null) {
                        itemsetMap.remove(removed.items);
                    }
                }

                updateThresholdLocked();
                return true;
            }
        }

        private void updateThresholdLocked() {  // Must be called under lock
            if (topKSet.size() >= k) {
                Itemset kthItem = topKSet.stream()
                    .skip(k - 1)
                    .findFirst()
                    .orElse(null);

                if (kthItem != null) {
                    threshold.set(kthItem.expectedUtility);
                }
            }
        }

        double getThreshold() {
            return threshold.get();
        }

        List<Itemset> getTopK() {
            synchronized (lock) {
                return topKSet.stream()
                    .limit(k)
                    .collect(Collectors.toList());
            }
        }
    }

    /**
     * Itemset result class
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

        // Read input files
        Map<Integer, Double> profits = readProfitTable(profitFile);
        List<Transaction> database = readDatabase(dbFile);

        System.out.println("=== PTK-HUIM-U± Enhanced Version 2.1 ===");
        System.out.println("Key improvements:");
        System.out.println("1. Enhanced thread safety with atomic operations");
        System.out.println("2. Dynamic RTWU-based branch pruning");
        System.out.println("3. Improved thread pool management");
        System.out.println("4. Better memory monitoring and statistics");
        System.out.println("5. Optimized configuration parameters");
        System.out.println();

        // Run enhanced algorithm
        ver3_1 algorithm = new ver3_1(profits, k, minPro);
        List<Itemset> topK = algorithm.mine(database);

        // Display results
        System.out.println("\n=== Top-" + k + " PHUIs ===");
        int rank = 1;
        for (Itemset itemset : topK) {
            System.out.printf("%d. %s\n", rank++, itemset);
        }
    }

    /**
     * Read profit table from file
     */
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

    /**
     * Read database from file
     */
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