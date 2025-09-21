package main.ver5;

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
 * VERSION 5.0 IMPROVEMENTS:
 * 1. Removed all duplicate/redundant code
 * 2. Unified parallel/sequential execution
 *
 * @author Optimized Implementation
 * @version 5.0
 */
public class ver5 {
    private final Map<Integer, Double> itemProfits;
    private final int k;
    private final double minPro;
    private static final double EPSILON = 1e-10;
    private static final double LOG_EPSILON = -700;

    // Thread-safe top-K management - simplified
    private final TopKManager topKManager;

    // Core data structures
    private Map<Integer, Integer> itemToRank;
    private Map<Integer, Double> itemRTWU;

    // Statistics tracking
    private final AtomicLong candidatesGenerated = new AtomicLong(0);
    private final AtomicLong candidatesPruned = new AtomicLong(0);
    private final AtomicLong utilityListsCreated = new AtomicLong(0);
    private final AtomicLong euPruned = new AtomicLong(0);
    private final AtomicLong epPruned = new AtomicLong(0);
    private final AtomicLong rtwuPruned = new AtomicLong(0);
    private final AtomicLong branchPruned = new AtomicLong(0);

    // Parallel execution control
    private final ForkJoinPool customThreadPool;
    private static final int PARALLEL_THRESHOLD = 30;
    private static final int TASK_GRANULARITY = 7;

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
                if (profit != null && profit > 0) {
                    rtu += profit * quantities[idx];
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
     * Optimized Utility-List with lazy computation
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
     * Unified ForkJoinTask for mining
     */
    private class MiningTask extends RecursiveAction {
        private final List<Integer> sortedItems;
        private final Map<Integer, EnhancedUtilityList> singleItemLists;
        private final int start;
        private final int end;

        MiningTask(List<Integer> sortedItems,
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
                // Process items directly
                for (int i = start; i < end; i++) {
                    processPrefix(i);
                }
            } else {
                // Split into subtasks
                int mid = start + (size / 2);
                MiningTask leftTask = new MiningTask(sortedItems, singleItemLists, start, mid);
                MiningTask rightTask = new MiningTask(sortedItems, singleItemLists, mid, end);
                invokeAll(leftTask, rightTask);
            }
        }

        private void processPrefix(int index) {
            Integer item = sortedItems.get(index);
            EnhancedUtilityList ul = singleItemLists.get(item);

            if (ul == null) return;

            // Check if branch should be pruned
            if (shouldPruneBranch(item)) {
                branchPruned.incrementAndGet();
                return;
            }

            // Get filtered extensions
            List<EnhancedUtilityList> extensions = getFilteredExtensions(
                sortedItems, singleItemLists, index
            );

            if (!extensions.isEmpty()) {
                searchWithExtensions(ul, extensions, singleItemLists);
            }
        }
    }

    /**
     * Constructor
     */
    public ver5(Map<Integer, Double> itemProfits, int k, double minPro) {
        this.itemProfits = Collections.unmodifiableMap(new HashMap<>(itemProfits));
        this.k = k;
        this.minPro = minPro;
        this.topKManager = new TopKManager(k);

        int numThreads = Runtime.getRuntime().availableProcessors();
        this.customThreadPool = new ForkJoinPool(numThreads);
    }

    /**
     * Main mining method
     */
    public List<Itemset> mine(List<Transaction> rawDatabase) {
        Instant start = Instant.now();

        System.out.println("=== PTK-HUIM-U± Version 5.0 ===");
        System.out.println("Database size: " + rawDatabase.size());
        System.out.println("Number of items: " + itemProfits.size());
        System.out.println("K: " + k + ", MinPro: " + minPro);
        System.out.println("Thread pool size: " + customThreadPool.getParallelism());

        // Phase 1: Initialization
        System.out.println("\nPhase 1: Single-pass initialization...");
        Map<Integer, EnhancedUtilityList> singleItemLists = initializeDatabase(rawDatabase);

        List<Integer> sortedItems = getSortedItemsByRank(singleItemLists.keySet());
        System.out.println("Items after filtering: " + sortedItems.size());

        // Process single items
        for (Integer item : sortedItems) {
            EnhancedUtilityList ul = singleItemLists.get(item);
            if (ul != null) {
                evaluateItemset(ul);
            }
        }

        // Phase 2: Mining
        System.out.println("\nPhase 2: Mining itemsets...");
        
        if (sortedItems.size() >= PARALLEL_THRESHOLD) {
            System.out.println("Using parallel processing for " + sortedItems.size() + " items");
            MiningTask rootTask = new MiningTask(sortedItems, singleItemLists, 0, sortedItems.size());
            customThreadPool.invoke(rootTask);
        } else {
            System.out.println("Using sequential processing for " + sortedItems.size() + " items");
            for (int i = 0; i < sortedItems.size(); i++) {
                processItemPrefix(i, sortedItems, singleItemLists);
            }
        }

        List<Itemset> results = topKManager.getTopK();

        Instant end = Instant.now();

        // Print statistics
        printStatistics(start, end, results);

        // Shutdown thread pool
        shutdownThreadPool();

        return results;
    }

    /**
     * Process a single item prefix
     */
    private void processItemPrefix(int index, List<Integer> sortedItems,
                                  Map<Integer, EnhancedUtilityList> singleItemLists) {
        Integer item = sortedItems.get(index);
        EnhancedUtilityList ul = singleItemLists.get(item);

        if (ul == null) return;

        if (shouldPruneBranch(item)) {
            branchPruned.incrementAndGet();
            return;
        }

        List<EnhancedUtilityList> extensions = getFilteredExtensions(
            sortedItems, singleItemLists, index
        );

        if (!extensions.isEmpty()) {
            searchWithExtensions(ul, extensions, singleItemLists);
        }
    }

    /**
     * Centralized branch pruning check
     */
    private boolean shouldPruneBranch(Integer item) {
        double currentThreshold = topKManager.getThreshold();
        Double rtwu = itemRTWU.get(item);
        return rtwu != null && rtwu < currentThreshold - EPSILON;
    }

    /**
     * Centralized extension filtering
     */
    private List<EnhancedUtilityList> getFilteredExtensions(
            List<Integer> sortedItems,
            Map<Integer, EnhancedUtilityList> singleItemLists,
            int currentIndex) {
        
        double currentThreshold = topKManager.getThreshold();
        List<EnhancedUtilityList> extensions = new ArrayList<>();
        
        for (int j = currentIndex + 1; j < sortedItems.size(); j++) {
            Integer extItem = sortedItems.get(j);
            EnhancedUtilityList extUL = singleItemLists.get(extItem);
            
            if (extUL == null) continue;
            
            Double rtwu = itemRTWU.get(extItem);
            if (rtwu != null && rtwu < currentThreshold - EPSILON) {
                rtwuPruned.incrementAndGet();
                continue;
            }
            
            extensions.add(extUL);
        }
        
        return extensions;
    }

    /**
     * Search with extensions
     */
    private void searchWithExtensions(EnhancedUtilityList prefix,
                                     List<EnhancedUtilityList> extensions,
                                     Map<Integer, EnhancedUtilityList> singleItemLists) {
        
        // Check if can prune entire branch
        if (canPruneExtensionBranch(extensions)) {
            candidatesPruned.addAndGet(extensions.size());
            return;
        }

        for (int i = 0; i < extensions.size(); i++) {
            EnhancedUtilityList extension = extensions.get(i);
            
            // Process extension
            EnhancedUtilityList joined = processExtension(prefix, extension);
            
            if (joined == null) continue;
            
            // Recursive search if needed
            if (i < extensions.size() - 1) {
                List<EnhancedUtilityList> newExtensions = filterRemainingExtensions(
                    extensions, i + 1
                );
                
                if (!newExtensions.isEmpty()) {
                    searchWithExtensions(joined, newExtensions, singleItemLists);
                }
            }
        }
    }

    /**
     * Check if entire extension branch can be pruned
     */
    private boolean canPruneExtensionBranch(List<EnhancedUtilityList> extensions) {
        if (extensions.size() <= 1) return false;
        
        double currentThreshold = topKManager.getThreshold();
        double minRTWU = Double.MAX_VALUE;
        
        for (EnhancedUtilityList ext : extensions) {
            if (ext.rtwu < minRTWU) {
                minRTWU = ext.rtwu;
            }
        }
        
        return minRTWU < currentThreshold - EPSILON;
    }

    /**
     * Process a single extension
     */
    private EnhancedUtilityList processExtension(EnhancedUtilityList prefix,
                                                EnhancedUtilityList extension) {
        
        double currentThreshold = topKManager.getThreshold();
        
        if (extension.rtwu < currentThreshold - EPSILON) {
            rtwuPruned.incrementAndGet();
            candidatesPruned.incrementAndGet();
            return null;
        }
        
        EnhancedUtilityList joined = join(prefix, extension);
        
        if (joined == null || joined.elements.isEmpty()) {
            return null;
        }
        
        utilityListsCreated.incrementAndGet();
        candidatesGenerated.incrementAndGet();
        
        // Apply pruning strategies
        if (!applyPruningStrategies(joined)) {
            return null;
        }
        
        // Evaluate for top-k
        evaluateItemset(joined);
        
        return joined;
    }

    /**
     * Apply all pruning strategies
     */
    private boolean applyPruningStrategies(EnhancedUtilityList ul) {
        double threshold = topKManager.getThreshold();
        
        // Existential probability pruning
        if (ul.existentialProbability < minPro - EPSILON) {
            epPruned.incrementAndGet();
            candidatesPruned.incrementAndGet();
            return false;
        }
        
        // EU + remaining pruning
        double sumEU = ul.getSumEU();
        double sumRemaining = ul.getSumRemaining();
        
        if (sumEU + sumRemaining < threshold - EPSILON) {
            euPruned.incrementAndGet();
            candidatesPruned.incrementAndGet();
            return false;
        }
        
        return true;
    }

    /**
     * Filter remaining extensions
     */
    private List<EnhancedUtilityList> filterRemainingExtensions(
            List<EnhancedUtilityList> extensions, int startIndex) {
        
        double currentThreshold = topKManager.getThreshold();
        List<EnhancedUtilityList> filtered = new ArrayList<>();
        
        for (int j = startIndex; j < extensions.size(); j++) {
            EnhancedUtilityList ext = extensions.get(j);
            
            if (ext.rtwu >= currentThreshold - EPSILON) {
                filtered.add(ext);
            } else {
                rtwuPruned.incrementAndGet();
            }
        }
        
        return filtered;
    }

    /**
     * Evaluate itemset for top-k
     */
    private void evaluateItemset(EnhancedUtilityList ul) {
        double sumEU = ul.getSumEU();
        double threshold = topKManager.getThreshold();
        
        if (sumEU >= threshold - EPSILON &&
            ul.existentialProbability >= minPro - EPSILON) {
            topKManager.tryAdd(ul.itemset, sumEU, ul.existentialProbability);
        }
    }

    /**
     * Initialize database
     */
    private Map<Integer, EnhancedUtilityList> initializeDatabase(List<Transaction> rawDatabase) {
        // Calculate RTWU
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
        System.out.println("Building global ordering...");
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

        // Build utility lists
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
        
        double joinedRTWU = Math.min(ul1.rtwu, ul2.rtwu);
        
        List<EnhancedUtilityList.Element> joinedElements = new ArrayList<>();
        
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
     * Print statistics
     */
    private void printStatistics(Instant start, Instant end, List<Itemset> results) {
        System.out.println("\n=== Mining Complete ===");
        System.out.println("Execution time: " + Duration.between(start, end).toMillis() + " ms");
        System.out.println("Candidates generated: " + candidatesGenerated.get());
        System.out.println("Utility lists created: " + utilityListsCreated.get());
        System.out.println("Pruning statistics:");
        System.out.println("  - RTWU pruned: " + rtwuPruned.get());
        System.out.println("  - Branches pruned: " + branchPruned.get());
        System.out.println("  - EU+remaining pruned: " + euPruned.get());
        System.out.println("  - Existential probability pruned: " + epPruned.get());
        System.out.println("  - Total pruned: " + candidatesPruned.get());
        System.out.println("Final threshold: " + String.format("%.4f", topKManager.getThreshold()));
        System.out.println("Top-K found: " + results.size());
    }

    /**
     * Shutdown thread pool
     */
    private void shutdownThreadPool() {
        customThreadPool.shutdown();
        try {
            if (!customThreadPool.awaitTermination(10, TimeUnit.SECONDS)) {
                customThreadPool.shutdownNow();
            }
        } catch (InterruptedException e) {
            customThreadPool.shutdownNow();
            Thread.currentThread().interrupt();
        }
    }

    /**
     * Simplified TopK Manager
     */
    private class TopKManager {
        private final int k;
        private final ConcurrentSkipListSet<Itemset> topKSet;
        private final ConcurrentHashMap<Set<Integer>, Itemset> topKMap;
        private volatile double threshold = 0.0;
        private final Object lock = new Object();

        TopKManager(int k) {
            this.k = k;
            this.topKSet = new ConcurrentSkipListSet<>((a, b) -> {
                int cmp = Double.compare(b.expectedUtility, a.expectedUtility);
                if (cmp != 0) return cmp;
                return Integer.compare(a.hashCode(), b.hashCode());
            });
            this.topKMap = new ConcurrentHashMap<>();
        }

        boolean tryAdd(Set<Integer> items, double eu, double ep) {
            // Quick check without lock
            if (eu < threshold - EPSILON) {
                return false;
            }

            // Check for existing
            Itemset existing = topKMap.get(items);
            if (existing != null && existing.expectedUtility >= eu - EPSILON) {
                return false;
            }

            // Add with lock
            synchronized (lock) {
                // Double-check after lock
                if (topKSet.size() >= k && eu < threshold - EPSILON) {
                    return false;
                }

                Itemset current = topKMap.get(items);
                if (current != null) {
                    if (current.expectedUtility >= eu - EPSILON) {
                        return false;
                    }
                    topKSet.remove(current);
                }

                Itemset newItemset = new Itemset(items, eu, ep);
                topKSet.add(newItemset);
                topKMap.put(items, newItemset);

                // Remove weakest if over k
                if (topKSet.size() > k) {
                    Itemset removed = topKSet.pollLast();
                    if (removed != null) {
                        topKMap.remove(removed.items);
                    }
                }

                // Update threshold
                if (topKSet.size() >= k) {
                    threshold = topKSet.last().expectedUtility;
                }
            }
            return true;
        }

        double getThreshold() {
            return threshold;
        }

        List<Itemset> getTopK() {
            return new ArrayList<>(topKSet);
        }
    }

    /**
     * Itemset class
     */
    static class Itemset {
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
                    ", prob=" + String.format("%.2f", probability) +
                    '}';
        }
    }

    /**
     * Transaction class
     */
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

    /**
     * Main method
     */
    public static void main(String[] args) throws IOException {
        if (args.length != 4) {
            System.err.println("Usage: PTKHUIMv5 <database_file> <profit_file> <k> <min_probability>");
            System.exit(1);
        }

        String dbFile = args[0];
        String profitFile = args[1];
        int k = Integer.parseInt(args[2]);
        double minPro = Double.parseDouble(args[3]);

        // Read input files
        Map<Integer, Double> profits = readProfitTable(profitFile);
        List<Transaction> database = readDatabase(dbFile);

        System.out.println("=== PTK-HUIM-U± Version 5.0 ===");
        System.out.println("Optimizations:");
        System.out.println("1. Removed all duplicate code");
        System.out.println("2. Unified mining approach");
        System.out.println("3. Centralized pruning strategies");
        System.out.println("4. Simplified TopK management");
        System.out.println("5. Optimized memory allocation");
        System.out.println();

        // Run algorithm
        ver5 algorithm = new ver5(profits, k, minPro);
        List<Itemset> topK = algorithm.mine(database);

        // Display results
        System.out.println("\n=== Top-" + k + " PHUIs ===");
        int rank = 1;
        for (Itemset itemset : topK) {
            System.out.printf("%d. %s\n", rank++, itemset);
        }
    }

    /**
     * Read profit table
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
     * Read database
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