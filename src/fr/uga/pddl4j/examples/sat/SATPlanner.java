//MacOS: javac -d classes -cp lib/pddl4j-4.0.0.jar:lib/org.sat4j.core.jar:lib/sat4j-sat.jar  src/fr/uga/pddl4j/examples/sat/SATPlanner.java
//MacOS: java -cp classes:lib/pddl4j-4.0.0.jar:lib/org.sat4j.core.jar:lib/sat4j-sat.jar fr.uga.pddl4j.examples.sat.SATPlanner src/test/blocks/strips-typed/domain.pddl src/test/blocks/strips-typed/p001.pddl

//Windows: javac -d classes -cp "lib/pddl4j-4.0.0.jar;lib/org.sat4j.core.jar;lib/sat4j-sat.jar" src/fr/uga/pddl4j/examples/sat/SATPlanner.java
//Windows: java -cp "classes;lib/pddl4j-4.0.0.jar;lib/org.sat4j.core.jar;lib/sat4j-sat.jar" fr.uga.pddl4j.examples.sat.SATPlanner src/test/blocks/strips-typed/domain.pddl src/test/blocks/strips-typed/p001.pddl

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
 * This class implements a simple SAT planner based on SAT4J et PDDL4J. 
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
     * Get the fluent ID for the time step specified
     */
    public int getFluentID(ADLProblem problem, Fluent state, int timeStep) {
        int idxState = problem.getFluents().indexOf(state);
        return (problem.getFluents().size() + problem.getActions().size()) * timeStep + 1 + idxState;
    }

    /**
     * Get the action ID for the time step specified
     */
    public int getActionID(Problem problem, Action action, int timeStep) {
        int idxAction = problem.getActions().indexOf(action);
        return (problem.getFluents().size() + problem.getActions().size()) * timeStep + 1 + problem.getFluents().size()
                + idxAction;
    }

    /**
     * Get the action with the index specified
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
     * Encode the initial state
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
     * Encode the goal state.
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
     * Encode the action.
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

    // Encode the fluents in the precondition of an action
    private void encodeFluentsPrecond(BitVector fluents, ADLProblem problem, int timeStep, int actionId, boolean isPositive, Vec<IVecInt> clauses) {
        for (int p = fluents.nextSetBit(0); p >= 0; p = fluents.nextSetBit(p + 1)) {

            Fluent fluent = problem.getFluents().get(p);
            int fluentId = getFluentID(problem, fluent, timeStep);
            VecInt clause = new VecInt(new int[] { -actionId, isPositive ? fluentId : -fluentId });

            clauses.push(clause);
            fluents.set(p);
        }
    }

    // Encode the fluents in the effect of an action
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
     * Encode the state transitions by step.
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
    
    // Create a frame axiom for a fluent
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
     * Encode the action disjunction.
     */
    public Vec<IVecInt> EncodeActionDisjunction(final ADLProblem problem, int planSize) {
        Vec<IVecInt> clauses = new Vec<IVecInt>();

        List<Action> actions = problem.getActions();
        for (int timeStep = 0; timeStep < planSize; timeStep++) {
            for (int i = 0; i < actions.size(); i++) {
                for (int j = i + 1; j < actions.size(); j++) {
                    Action a1 = actions.get(i);
                    Action a2 = actions.get(j);

                    if (areContradictoryActions(a1, a2)) {
                        int a1Id = getActionID(problem, a1, timeStep);
                        int a2Id = getActionID(problem, a2, timeStep);
                        clauses.push(new VecInt(new int[] { -a1Id, -a2Id }));
                    }
                }
            }
        }
        return clauses;
    }

    // Check if two actions are contradictory
    private boolean areContradictoryActions(Action a1, Action a2) {
        BitVector a1PosEffects = a1.getUnconditionalEffect().getPositiveFluents();
        BitVector a1NegEffects = a1.getUnconditionalEffect().getNegativeFluents();

        BitVector a2PosEffects = a2.getUnconditionalEffect().getPositiveFluents();
        BitVector a2NegEffects = a2.getUnconditionalEffect().getNegativeFluents();

        BitVector a1PrePos = a1.getPrecondition().getPositiveFluents();
        BitVector a1PreNeg = a1.getPrecondition().getNegativeFluents();
        BitVector a2PrePos = a2.getPrecondition().getPositiveFluents();
        BitVector a2PreNeg = a2.getPrecondition().getNegativeFluents();

        if (a1PosEffects.intersects(a2NegEffects) || a2PosEffects.intersects(a1NegEffects)) {
            return true;
        }

        if (a1PosEffects.intersects(a2PreNeg) || a1NegEffects.intersects(a2PrePos)) {
            return true;
        }

        if (a2PosEffects.intersects(a1PreNeg) || a2NegEffects.intersects(a1PrePos)) {
            return true;
        }

        if (a1PrePos.intersects(a2NegEffects) || a1PreNeg.intersects(a2PosEffects)) {
            return true;
        }

        return false;
    }

    /**
     * Use a SAT solver to check if a problem is satisfiable and to find a model.
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
     * Encode the problem to a SAT problem.
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
                LOGGER.error("No solution found\n");
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



    


