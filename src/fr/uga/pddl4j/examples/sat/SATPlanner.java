// javac -d classes -cp lib/pddl4j-4.0.0.jar:lib/org.sat4j.core.jar:lib/sat4j-sat.jar  src/fr/uga/pddl4j/examples/sat/SATPlanner.java
// java -cp classes:lib/pddl4j-4.0.0.jar:lib/org.sat4j.core.jar:lib/sat4j-sat.jar fr.uga.pddl4j.examples.sat.SATPlanner src/test/blocks/strips-typed/domain.pddl src/test/blocks/strips-typed/p001.pddl
package fr.uga.pddl4j.examples.sat;

import java.util.ArrayList;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

import fr.uga.pddl4j.parser.ParsedProblem;
import fr.uga.pddl4j.plan.Plan;
import fr.uga.pddl4j.plan.SequentialPlan;
import fr.uga.pddl4j.planners.AbstractPlanner;
import fr.uga.pddl4j.problem.ADLProblem;
import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.util.BitVector;
import picocli.CommandLine;

/**
 * This class implements a simple SAT planner based on SAT4J.
 *
 * @author H. Fiorino
 * @version 1.0 - 29.03.2021
 */
@CommandLine.Command(
    name = "SATPlanner", 
    version = "SAT 1.0", 
    description = "Solves a specified planning problem using SAT Planner.", 
    sortOptions = false, mixinStandardHelpOptions = true, headerHeading = "Usage:%n", 
    synopsisHeading = "%n", descriptionHeading = "%nDescription:%n%n", 
    parameterListHeading = "%nParameters:%n", 
    optionListHeading = "%nOptions:%n")
public final class SATPlanner extends AbstractPlanner<ADLProblem> {

    /**
     * The logger of the planner.
     */
    private static final Logger LOGGER = LogManager.getLogger(SATPlanner.class.getName());

    /**
     * Number of step of the bounding problem.
     */
    private int sizePlan = 1;
    /**
     * Command line option to set the number of step of the bounding problem.
     * 
     * @param sizePlan Number of step of the bounding problem
     */
    @CommandLine.Option(names = { "-s",
            "--size-plan" }, paramLabel = "<sizePlan>", description = "Number of step of the bounding problem")
    public void setSizePlan(final int sizePlan) {
        if (sizePlan < 0) {
            throw new IllegalArgumentException("Size plan must be greater than 0");
        }
        this.sizePlan = sizePlan;
    }

    /**
     * Get the fluent unique ID for the time step specified. To encode a problem as
     * a CNF formula, there must be an unique ID for each state
     * and each action at each time step.
     * The encodage of the unique ID for a state or an action is as follow:
     * <ul>
     * <li>1 -> idx of fluent 0 at time step 0</li>
     * <li>2 -> idx of fluent 1 at time step 0</li>
     * <li>...</li>
     * <li>N + 1-> idx of fluent N at time step 0</li>
     * <li>N + 2-> idx of action 0 at time step 0</li>
     * <li>...</li>
     * <li>N + M + 1 -> idx of action M at time step 0</li>
     * <li>N + M + 2 -> idx of fluent 0 at time step 1</li>
     * <li>...</li>
     * <li>(N + M) * n + 1-> idx of action M at time step n</li>
     * </ul>
     * 
     * @param problem  The problem to solve
     * @param state    The state to find the unique ID
     * @param timeStep The time step of the fluent
     * @return The unique ID of the fluent (i.e unique ID of the state at the given
     *         time step)
     */
    public int getFluentID(ADLProblem problem, Fluent state, int timeStep) {
        int idxState = problem.getFluents().indexOf(state);
        return (problem.getFluents().size() + problem.getActions().size()) * timeStep + 1 + idxState;
    }

    /**
     * Get the action unique ID for the time step specified. To encode a problem as
     * a CNF formula, there must be an unique ID for each state
     * and each action at each time step.
     * The encodage of the unique ID for a state or an action is as follow:
     * <ul>
     * <li>1 -> idx of fluent 0 at time step 0</li>
     * <li>2 -> idx of fluent 1 at time step 0</li>
     * <li>...</li>
     * <li>N + 1-> idx of fluent N at time step 0</li>
     * <li>N + 2-> idx of action 0 at time step 0</li>
     * <li>...</li>
     * <li>N + M + 1 -> idx of action M at time step 0</li>
     * <li>N + M + 2 -> idx of fluent 0 at time step 1</li>
     * <li>...</li>
     * <li>(N + M) * n + 1-> idx of action M at time step n</li>
     * </ul>
     * 
     * @param problem  The problem to solve
     * @param action   The action to find the unique ID
     * @param timeStep The time step of the action
     * @return The unique ID of the action (i.e unique ID of the action at the given
     *         time step)
     */
    public int getActionID(Problem problem, Action action, int timeStep) {
        int idxAction = problem.getActions().indexOf(action);
        return (problem.getFluents().size() + problem.getActions().size()) * timeStep + 1 + problem.getFluents().size()
                + idxAction;
    }

    /**
     * Given an unique ID (each state and each action are given an unique ID for
     * each
     * time step of the problem to allow the encoding of the problem into a CNF
     * formula), find the action linked to this ID.
     * 
     * @param problem        The problem to solve
     * @param actionUniqueID Unique ID of an action
     * @return The action object linked to this ID if exist, else null
     */
    public Action getActionWithIdx(Problem problem, int actionUniqueID) {

        if (actionUniqueID <= 0) {
            return null;
        }

        int idx = (actionUniqueID - 1) % (problem.getFluents().size() + problem.getActions().size());

        if (idx >= problem.getFluents().size()) {
            return problem.getActions().get(idx - problem.getFluents().size());
        } else {
            return null;
        }
    }

    /**
     * Encode the initial state as a CNF formula in dimacs format.
     * @param problem The problem to solve
     * @param planSize The size of the plan
     * @return The CNF formula in dimacs format
     * 
     */
    public Vec<IVecInt> encodeInitialState(ADLProblem problem, int planSize) {
        Vec<IVecInt> clauses = new Vec<IVecInt>();
        BitVector posFluents = problem.getInitialState().getPositiveFluents();
        List<Fluent> allFluents = problem.getFluents();

    
        for (int i = 0; i < allFluents.size(); i++) {
            Fluent fluent = allFluents.get(i);

            if (posFluents.get(i)) {
                IVecInt clause = new VecInt(new int[] { getFluentID(problem, fluent, 0) });
                clauses.push(clause);
                posFluents.set(i);
            } else {
                IVecInt clause = new VecInt(new int[] { -(getFluentID(problem, fluent, 0)) });
                clauses.push(clause);
            }
            
        }
        return clauses;
    }

    /**
     * Encode the goal state as a CNF formula in dimacs format.
     * @param problem The problem to solve
     * @param planSize The size of the plan
     * @return The CNF formula in dimacs format
     * 
     */
    public Vec<IVecInt> encodeGoalState(ADLProblem problem, int planSize) {
        Vec<IVecInt> clauses = new Vec<IVecInt>();
        BitVector posFluents = problem.getGoal().getPositiveFluents();
        
        for (int p = posFluents.nextSetBit(0); p >= 0; p = posFluents.nextSetBit(p + 1)) {
            
                Fluent fluent = problem.getFluents().get(p);
                IVecInt clause = new VecInt(new int[] { getFluentID(problem, fluent, planSize) });
                clauses.push(clause);

                posFluents.set(p);
        }
        return clauses;
    }

    /**
     * Encode the action as a CNF formula in dimacs format.
     * @param problem The problem to solve
     * @param action The action to encode
     * @param timeStep The time step of the action
     * @return The CNF formula in dimacs format
     * 
     */
    public Vec<IVecInt> encodeActions(final ADLProblem problem, int planSize) {
        Vec<IVecInt> clausesActions = new Vec<IVecInt>();

        for (int timeStep = 0; timeStep < planSize; timeStep++) {
            for (Action action : problem.getActions()) {
                int actionId = getActionID(problem, action, timeStep);
                BitVector prePosFluents = action.getPrecondition().getPositiveFluents();
                BitVector preNegFluents = action.getPrecondition().getNegativeFluents();

                // Encode positive and negative preconditions
                encodeFluentsPrecond(prePosFluents, problem, timeStep, actionId, true, clausesActions);
                encodeFluentsPrecond(preNegFluents, problem, timeStep, actionId, false, clausesActions);

                // Encode positive and negative effects
                BitVector effPosFluents = action.getUnconditionalEffect().getPositiveFluents();
                BitVector effNegFluents = action.getUnconditionalEffect().getNegativeFluents();
                encodeFluentsEff(effPosFluents, problem, timeStep, actionId, true, clausesActions);
                encodeFluentsEff(effNegFluents, problem, timeStep, actionId, false, clausesActions);
            }
        }

        return clausesActions;
    }


    private void encodeFluentsPrecond(BitVector fluents, ADLProblem problem, int timeStep, int actionId, boolean isPositive, Vec<IVecInt> clauses) {
        for (int p = fluents.nextSetBit(0); p >= 0; p = fluents.nextSetBit(p + 1)) {

            Fluent fluent = problem.getFluents().get(p);
            int fluentId = getFluentID(problem, fluent, timeStep);
            VecInt clause = new VecInt(new int[] { -actionId, isPositive ? fluentId : -fluentId });

            clauses.push(clause);
            fluents.set(p);
        }
    }

    private void encodeFluentsEff(BitVector fluents, ADLProblem problem, int timeStep, int actionId, boolean isPositive, Vec<IVecInt> clauses) {
        for (int p = fluents.nextSetBit(0); p >= 0; p = fluents.nextSetBit(p + 1)) {

            Fluent fluent = problem.getFluents().get(p);
            int fluentId = getFluentID(problem, fluent, timeStep+1);
            VecInt clause = new VecInt(new int[] { -actionId, isPositive ? fluentId : -fluentId });

            clauses.push(clause);
            fluents.set(p);
        }
    }

    /**
     * Encode the explanatory frame axioms as a CNF formula in dimacs format.
     * 
     * @param problem  The problem to solve
     * @param planSize Size of the plan
     * @return A vector of set (VecInt) of litterals in the Dimacs format
     */
    public Vec<IVecInt> encodeStateTransitionsByStep(final ADLProblem problem, int planSize) {
        Vec<IVecInt> clauses = new Vec<IVecInt>();
        List<Action> actions = problem.getActions();
        List<Fluent> fluents = problem.getFluents();
    
        // Initialize action lists for each fluent
        List<List<Action>> posEffects = new ArrayList<>(fluents.size());
        List<List<Action>> negEffects = new ArrayList<>(fluents.size());
        for (int i = 0; i < fluents.size(); i++) {
            posEffects.add(new ArrayList<>());
            negEffects.add(new ArrayList<>());
        }
    
        // Assign actions to fluents' effects
        for (Action action : actions) {
            for (int p = action.getUnconditionalEffect().getPositiveFluents().nextSetBit(0); p >= 0; p = action.getUnconditionalEffect().getPositiveFluents().nextSetBit(p + 1)) {
                posEffects.get(p).add(action);
            }
            for (int p = action.getUnconditionalEffect().getNegativeFluents().nextSetBit(0); p >= 0; p = action.getUnconditionalEffect().getNegativeFluents().nextSetBit(p + 1)) {
                negEffects.get(p).add(action);
            }
        }
    
        // Construct frame axioms for each fluent and timestep
        for (int i = 0; i < fluents.size(); i++) {
            Fluent f = fluents.get(i);
            for (int timeStep = 0; timeStep < planSize; timeStep++) {
                if (!posEffects.get(i).isEmpty()) {
                    clauses.push(createFrameAxiom(f, posEffects.get(i), timeStep, true, problem));
                }
                if (!negEffects.get(i).isEmpty()) {
                    clauses.push(createFrameAxiom(f, negEffects.get(i), timeStep, false, problem));
                }
            }
        }
    
        return clauses;
    }
    
    private VecInt createFrameAxiom(Fluent fluent, List<Action> actions, int timeStep, boolean isPositive, ADLProblem problem) {
        VecInt clause = new VecInt();
        int fluentId1 = getFluentID(problem, fluent, timeStep);
        int fluentId2 = getFluentID(problem, fluent, timeStep + 1);
        clause.push(isPositive ? fluentId1 : -fluentId1);
        clause.push(isPositive ? -fluentId2 : fluentId2);
        for (Action action : actions) {
            clause.push(getActionID(problem, action, timeStep));
        }
        return clause;
    }
    

    /**
     * Encode the complete exclusion axioms as a CNF formula in dimacs format.
     * 
     * @param problem  The problem to solve
     * @param planSize Size of the plan
     * @return A vector of set (VecInt) of litterals in the Dimacs format
     */
    public Vec<IVecInt> EncodeActionDisjunction(final ADLProblem problem, int planSize) {

        Vec<IVecInt> clauses = new Vec<IVecInt>();

        for (int iterAction1 = 0; iterAction1 < problem.getActions().size(); iterAction1++) {
            for (int iterAction2 = 0; iterAction2 < iterAction1; iterAction2++) {

                Action action1 = problem.getActions().get(iterAction1);
                Action action2 = problem.getActions().get(iterAction2);

                int initAction1Idx = getActionID(problem, action1, 0);
                int initAction2Idx = getActionID(problem, action2, 0);

                int offsetToNextActionIdx = problem.getActions().size() + problem.getFluents().size();

                for (int timeStep = 0; timeStep < planSize; timeStep++) {

                    int offset = offsetToNextActionIdx * timeStep;
                    VecInt clause = new VecInt( new int[] { -(initAction1Idx + offset), -(initAction2Idx + offset) });
                    clauses.push(clause);
                }
            }
        }

        return clauses;
    }

    /**
     * Use a SAT solver to check if a problem is satisfiable and to find a model.
     * 
     * @param clauses The CNF formula in dimacs format
     * @param problem The problem to solve
     * @return The model of the problem if it exists, else null
     * @throws TimeoutException
     */

    public int[] solveSAT(Vec<IVecInt> clauses, ADLProblem problem) throws TimeoutException {

        LOGGER.info(clauses.size() + " clauses\n");
        ISolver solver = SolverFactory.newDefault();

        solver.newVar((problem.getFluents().size() + problem.getActions().size()) * sizePlan  + problem.getFluents().size());
        solver.setExpectedNumberOfClauses(clauses.size());

        try {
            solver.addAllClauses(clauses);
        } catch (ContradictionException e) {
            LOGGER.error("Contradiction exception\n");
            return null;
        }

        IProblem problemSAT = solver;
        try {
            if (problemSAT.isSatisfiable()) {
                LOGGER.info("Is satisfiable !\n");
                return problemSAT.model();
            } else {
                LOGGER.error("Is not satisfiable !\n");
                return null;
            }
        } catch (TimeoutException e) {
            throw e;
        }

    }

    /**
     * Encode the problem as a CNF formula in dimacs format.
     * 
     * @param problem  Problem to encode
     * @param planSize Size of the plan
     * @return A vector of set (VecInt) of litterals in the Dimacs format
     */
    public Vec<IVecInt> encodeProblem(final ADLProblem problem, int planSize) {
        Vec<IVecInt> clausesInitState = encodeInitialState(problem, planSize);
        Vec<IVecInt> clausesGoalState = encodeGoalState(problem, planSize);
        Vec<IVecInt> clausesActions = encodeActions(problem, planSize);
        Vec<IVecInt> clausesExplanatoryFrameAxioms = encodeStateTransitionsByStep(problem, planSize);
        Vec<IVecInt> clausesCompleteExclusionAxioms = EncodeActionDisjunction(problem, planSize);

        Vec<IVecInt> clauses = new Vec<IVecInt>();
        clausesInitState.copyTo(clauses);
        clausesGoalState.copyTo(clauses);
        clausesActions.copyTo(clauses);
        clausesExplanatoryFrameAxioms.copyTo(clauses);
        clausesCompleteExclusionAxioms.copyTo(clauses);

        return clauses;
    }

    /**
     * Decode the model of the problem to a plan.
     * 
     * @param model  The model of the problem
     * @param problem The problem to solve
     * @return The plan of the problem
     */
    public Plan decodePlan(int[] model, ADLProblem problem) {
        Plan plan = new SequentialPlan();
        int idxAction = 0;
        for (Integer i : model) {
            Action a = getActionWithIdx(problem, i);
            if (a != null) {
                plan.add(idxAction, a);
                idxAction++;
            }
        }
        return plan;
    }

    @Override
    public Plan solve(ADLProblem problem) {
        int[] model;
        while(true) {
            long startEncodeTime = System.currentTimeMillis();
            Vec<IVecInt> clauses = encodeProblem(problem, sizePlan);
            long endEncodeTime = System.currentTimeMillis();
            this.getStatistics().setTimeToEncode(this.getStatistics().getTimeToEncode() + (endEncodeTime - startEncodeTime));

            long startTime = System.currentTimeMillis();
            try {
                model = solveSAT(clauses, problem);
            } catch (TimeoutException e) {
                long endTime = System.currentTimeMillis();
                this.getStatistics().setTimeToSearch(this.getStatistics().getTimeToSearch() + (endTime - startTime));
                LOGGER.error("Timeout exception");
                return null;
            }
            long endTime = System.currentTimeMillis();
                this.getStatistics().setTimeToSearch(this.getStatistics().getTimeToSearch() + (endTime - startTime));

            if (model == null) {
                LOGGER.error("No solution found");
                this.sizePlan *= 2;
            } else {
                break;
            }
        }

        return decodePlan(model, problem);
    }

    /**
     * The main method of the <code>SAT</code> planner.
     *
     * @param args the arguments of the command line.
     */
    public static void main(String[] args) {
        try {
            final SATPlanner planner = new SATPlanner();
            CommandLine cmd = new CommandLine(planner);
            cmd.execute(args);
        } catch (IllegalArgumentException e) {
            LOGGER.fatal(e.getMessage());
        }
    }

    @Override
    public ADLProblem instantiate(ParsedProblem problem) {
        final ADLProblem pb = new ADLProblem(problem);
        pb.instantiate();
        return pb;
    }

}



    


