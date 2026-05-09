package nl.tudelft.instrumentation.fuzzing;

import java.util.*;

/**
 * You should write your own solution using this class.
 */
public class FuzzingLab {
        static Random r = new Random();
        static List<String> currentTrace;
        static int traceLength = 10;
        static boolean isFinished = false;

        static Set<String> coveredBranches = new HashSet<>();
        static Set<String> foundErrors = new HashSet<>();

        static double currentRunDistance = 0.0;
        static double bestDistance = Double.MAX_VALUE;

        static final int NO_IMPROVEMENT_LIMIT = 100;

        static void initialize(String[] inputSymbols) {
                currentTrace = generateRandomTrace(inputSymbols);
        }

        /**
         * Compute the branch distance for a given condition and the branch that was
         * actually taken. Returns 0 when the branch is satisfied, a positive value
         * proportional to how far the inputs are from satisfying it.
         *
         * @param condition the condition MyVar (may be BINARY, UNARY, BOOL, etc.)
         * @param taken     the boolean value that the condition evaluated to
         * @return branch distance (0 = satisfied, >0 = not satisfied)
         */
        static double branchDistance(MyVar condition, boolean taken) {
                if (condition == null)
                        return 1.0;

                switch (condition.type) {
                        case BOOL:
                                return (condition.value == taken) ? 0.0 : 1.0;

                        case INT:
                                boolean intAsBool = condition.int_value != 0;
                                return (intAsBool == taken) ? 0.0 : 1.0;

                        case UNARY:
                                if ("!".equals(condition.operator)) {
                                        // !x taken as `taken` means x was !taken
                                        return branchDistance(condition.left, !taken);
                                }
                                return 1.0;

                        case BINARY:
                                return binaryBranchDistance(condition, taken);

                        default:
                                return 1.0;
                }
        }

        /**
         * Branch distance for binary expressions. Handles int and string operands.
         */
        static double binaryBranchDistance(MyVar condition, boolean taken) {
                MyVar lv = condition.left;
                MyVar rv = condition.right;
                String op = condition.operator;

                // String equality — use edit distance
                if (lv != null && rv != null
                                && lv.type == TypeEnum.STRING && rv.type == TypeEnum.STRING) {
                        int dist = editDistance(lv.str_value, rv.str_value);
                        switch (op) {
                                case "==":
                                        return taken ? dist : (dist == 0 ? 1.0 : 0.0);
                                case "!=":
                                        return taken ? (dist == 0 ? 1.0 : 0.0) : dist;
                                default:
                                        return 1.0;
                        }
                }

                // Integer arithmetic
                if (lv != null && rv != null
                                && lv.type == TypeEnum.INT && rv.type == TypeEnum.INT) {
                        int l = lv.int_value;
                        int rr = rv.int_value;
                        switch (op) {
                                case "==":
                                        return taken ? Math.abs(l - rr) : (l == rr ? 1.0 : 0.0);
                                case "!=":
                                        return taken ? (l == rr ? 1.0 : 0.0) : Math.abs(l - rr);
                                case "<":
                                        return taken ? Math.max(0, l - rr + 1) : Math.max(0, rr - l);
                                case "<=":
                                        return taken ? Math.max(0, l - rr) : Math.max(0, rr - l + 1);
                                case ">":
                                        return taken ? Math.max(0, rr - l + 1) : Math.max(0, l - rr);
                                case ">=":
                                        return taken ? Math.max(0, rr - l) : Math.max(0, l - rr + 1);
                                default:
                                        return 1.0;
                        }
                }

                // Boolean && and || — recursive decomposition
                if ("&&".equals(op)) {
                        if (taken) {
                                // Both sides must be true
                                return branchDistance(lv, true) + branchDistance(rv, true);
                        } else {
                                // At least one side must be false — take the minimum
                                return Math.min(branchDistance(lv, false), branchDistance(rv, false));
                        }
                }
                if ("||".equals(op)) {
                        if (taken) {
                                return Math.min(branchDistance(lv, true), branchDistance(rv, true));
                        } else {
                                return branchDistance(lv, false) + branchDistance(rv, false);
                        }
                }

                return 1.0;
        }

        /**
         * Levenshtein edit distance between two strings.
         */
        static int editDistance(String a, String b) {
                int m = a.length(), n = b.length();
                int[][] dp = new int[m + 1][n + 1];
                for (int i = 0; i <= m; i++)
                        dp[i][0] = i;
                for (int j = 0; j <= n; j++)
                        dp[0][j] = j;
                for (int i = 1; i <= m; i++) {
                        for (int j = 1; j <= n; j++) {
                                if (a.charAt(i - 1) == b.charAt(j - 1)) {
                                        dp[i][j] = dp[i - 1][j - 1];
                                } else {
                                        dp[i][j] = 1 + Math.min(dp[i - 1][j - 1],
                                                        Math.min(dp[i - 1][j], dp[i][j - 1]));
                                }
                        }
                }
                return dp[m][n];
        }

        /**
         * Called each time a branch fires during SUT execution. Tracks coverage and
         * accumulates branch distance for the current trace.
         */
        static void encounteredNewBranch(MyVar condition, boolean value, int line_nr) {
                String branchId = line_nr + ":" + value;
                coveredBranches.add(branchId);

                // Accumulate distance toward the branch that was NOT taken
                double dist = branchDistance(condition, !value);
                currentRunDistance += dist;
        }

        /**
         * Produce a mutated version of currentTrace.
         */
        static List<String> fuzz(String[] inputSymbols) {
                List<String> mutated = new ArrayList<>(currentTrace);

                // Apply 1–3 mutations to avoid getting stuck in local optima
                int numMutations = 1 + r.nextInt(3);
                for (int m = 0; m < numMutations; m++) {
                        int op = r.nextInt(4);
                        switch (op) {
                                case 0: // Replace a random symbol
                                        mutated.set(r.nextInt(mutated.size()),
                                                        inputSymbols[r.nextInt(inputSymbols.length)]);
                                        break;
                                case 1: // Insert a random symbol
                                        mutated.add(r.nextInt(mutated.size() + 1),
                                                        inputSymbols[r.nextInt(inputSymbols.length)]);
                                        break;
                                case 2: // Delete a random symbol
                                        if (mutated.size() > 1)
                                                mutated.remove(r.nextInt(mutated.size()));
                                        break;
                                case 3: // Swap two symbols
                                        if (mutated.size() > 1) {
                                                int i = r.nextInt(mutated.size());
                                                int j = r.nextInt(mutated.size());
                                                Collections.swap(mutated, i, j);
                                        }
                                        break;
                        }
                }
                return mutated;
        }

        /**
         * Generate a random trace from an array of symbols.
         */
        static List<String> generateRandomTrace(String[] symbols) {
                ArrayList<String> trace = new ArrayList<>();
                for (int i = 0; i < traceLength; i++) {
                        trace.add(symbols[r.nextInt(symbols.length)]);
                }
                return trace;
        }

        static void run() {
                initialize(DistanceTracker.inputSymbols);

                int noImprovement = 0;
                List<String> bestTrace = new ArrayList<>(currentTrace);

                while (!isFinished) {
                        int coverageBefore = coveredBranches.size();
                        currentRunDistance = 0.0;

                        DistanceTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));

                        int coverageAfter = coveredBranches.size();
                        boolean improved = coverageAfter > coverageBefore
                                        || currentRunDistance < bestDistance;

                        if (improved) {
                                bestTrace = new ArrayList<>(currentTrace);
                                bestDistance = currentRunDistance;
                                noImprovement = 0;
                                System.out.println("Coverage: " + coverageAfter
                                                + " branches | Errors found: " + foundErrors.size());
                        } else {
                                noImprovement++;
                        }

                        if (noImprovement >= NO_IMPROVEMENT_LIMIT) {
                                // Random restart — escape local optimum
                                System.out.println("=== Random restart triggered ===");
                                System.out.println("Coverage: " + coveredBranches.size() + " branches");
                                if (foundErrors.isEmpty()) {
                                        System.out.println("Errors found: none yet");
                                } else {
                                        System.out.println("Errors found (" + foundErrors.size() + "):");
                                        for (String err : foundErrors) {
                                                System.out.println("  " + err);
                                        }
                                }
                                System.out.println("================================");
                                currentTrace = generateRandomTrace(DistanceTracker.inputSymbols);
                                bestDistance = Double.MAX_VALUE;
                                noImprovement = 0;
                        } else if (noImprovement > NO_IMPROVEMENT_LIMIT / 2) {

                                // Half-stuck: mix best trace with a fresh random trace
                                List<String> fresh = generateRandomTrace(DistanceTracker.inputSymbols);
                                List<String> hybrid = new ArrayList<>(bestTrace);
                                int pivot = r.nextInt(hybrid.size());
                                for (int i = pivot; i < Math.min(hybrid.size(), fresh.size()); i++) {
                                        hybrid.set(i, fresh.get(i));
                                }
                                currentTrace = hybrid;
                        } else {
                                // Normal case: mutate the best trace found so far
                                currentTrace = fuzz(DistanceTracker.inputSymbols);
                        }
                }
        }

        /**
         * Catches SUT output. Errors printed by the RERS SUT start with "Error".
         */
        public static void output(String out) {
                if (out.startsWith("Found a new branch:")) {
                        return;
                } else if (out.contains("error")) {
                        if (foundErrors.add(out)) {
                                System.out.println("[NEW ERROR] " + out
                                                + " | trace: " + currentTrace);
                        }
                } else {
                        System.out.println(out);
                }
        }
}
