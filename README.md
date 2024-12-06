# SAT_Planner

# Dossier Figures pour les figures de chaque benchmark réalisé
At first, run 
```
javac -d classes -cp lib/pddl4j-4.0.0.jar:lib/org.sat4j.core.jar:lib/sat4j-sat.jar  src/fr/uga/pddl4j/examples/sat/SATPlanner.java
```

Then the two bash files : run_tests.sh and run_tests_with_HSP.sh can run automaically all the tests in the folder src/test/* and create the summary file on .csv in the folder results and results_hsp  

so run 
```
chmod +x run_tests.sh
```

```
./run_tests.sh
```
or 
```
chmod +x run_tests_with_HSP.sh
```

```
./run_tests_with_HSP.sh
```

and to Check plan validity we can just run for exemple : 

```
./VAL/bin/Validate src/test/blocks/strips-typed/domain.pddl src/test/blocks/strips-typed/p001.pddl results/blocks/p001plan.txt
```