package pku;

import java.io.*;
import java.util.HashMap;
import java.util.HashSet;
import java.util.TreeSet;

import javax.script.SimpleBindings;

import pascal.taie.util.graph.Edge;
import pascal.taie.util.graph.Graph;
import pascal.taie.util.graph.SimpleGraph;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import pascal.taie.World;
import pascal.taie.analysis.ProgramAnalysis;
import pascal.taie.config.AnalysisConfig;

import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.StoreArray;

public class Pair<A, B> {
    private final A first;
    private final B second;

    public Pair(A first, B second) {
        this.first = first;
        this.second = second;
    }

    public getFirst() {
        return this.first;
    }

    public getSecond() {
        return this.second;
    }
}

public class PointerAnalysis extends PointerAnalysisTrivial
{
    public static final String ID = "pku-pta";

    // TODO: Change the definition of these parameters
    public SimpleGraph<Exp> pointerFlowGraph;
    public SimpleGraph<JMethod> callGraph; // Is that Good?
    public Queue<Pair<Exp, HashSet<Integer>>> workList;
    public HashSet<JMethod> reachableMethods;
    public HashSet<Stmt> reachableStatements;
    public HashMap<Exp, HashSet<Integer>> pointsToSet;

    

    public PointerAnalysis(AnalysisConfig config) {
        super(config);
        pointerFlowGraph = new SimpleGraph<Exp>();
        callGraph = new SimpleGraph<Exp>(); // Is that correct?
        workList = new Queue<Pair<Exp, HashSet<Integer>>>();
        reachableMethods = new HashSet<JMethod>();
        reachableStatements = new HashSet<Stmt>();
        pointsToSet = new HashMap<Exp, HashSet<Integer>>();
    }

    @Override
    public PointerAnalysisResult analyze() {
        var result = new PointerAnalysisResult();
        var preprocess = new PreprocessResult();
        var world = World.get();
        var main = world.getMainMethod();
        var jclass = main.getDeclaringClass();

        // You need to use `preprocess` like in PointerAnalysisTrivial
        // when you enter one method to collect infomation given by
        // Benchmark.alloc(id) and Benchmark.test(id, var)
        //
        // As for when and how you enter one method,
        // it's your analysis assignment to accomplish
        /*logger.info("The main method is {}", main.getName());
        logger.info("JClass is {}", jclass.getName());
        jclass.getDeclaredMethods().forEach(method->{
            logger.info("This method is {}", method.getName());
            if(!method.isAbstract())
                preprocess.analysis(method.getIR());            
        });
        
        //return super.analyze();
        var objs = new TreeSet<>(preprocess.obj_ids.values());

        preprocess.test_pts.forEach((test_id, pt)->{
            result.put(test_id, objs);
        });

        dump(result);*/
    
        // TODO: Finish the Solve() function in the slide
        addReachable(main);
        while (!workList.isEmpty()) {
            Pair<Exp, HashSet<Integer>> entry = workList.poll();
            Exp n = entry.getFirst();
            HashSet<Integer> delta = entry.getSecond();
            delta.removeAll(pointsToSet.get(workList.getFirst()));
            if (!delta.isEmpty()) {
                propagate(n, delta);
                if (n instanceof Var) {
                    delta.forEach(obj->{
                        reachableStatements.forEach(stmt->{
                            if (stmt instanceof FieldStmt<?, ?>) {
                                if (stmt instanceof LoadField) {

                                }
                                else if (stmt instanceof StoreField) {

                                }
                            }
                        });
                    });
                }
            }

        }

        return result;
    }

    public void addReachable(JMethod method)
    {
        PreprocessResult preprocess = method.getIR().getResult("pku-pta-preprocess"); // Preprocess the method

        if (!reachableMethods.contains(method)) {
            reachableMethods.add(method);
            var stmts = method.getIR().getStmts();
            stmts.forEach(stmt->{
                if (!reachableStatements.contains(stmt)) {
                    reachableStatements.add(stmt);
                }
                if (stmt instanceof AssignStmt<?, ?>) {
                    if (stmt instanceof New) {
                        var lval = ((New) stmt).getLValue();
                        HashSet<Integer> pts = new HashSet<Integer>();
                        pts.add(preprocess.getObjIdAt(stmt));
                        workList.offer(new Pair<Exp, HashSet<Integer>>((Exp) lval, pts));
                    } else if (stmt instanceof Copy) {
                        var lval = ((Copy) stmt).getLValue();
                        var rval = ((Copy) stmt).getRValue();
                        addEdge(rval, xval);
                    }
                }
            });
        }
    }

    public void processCall(Var v, New stmt) {
        // TODO: Finish the processCall function in the slide
        return;
    }

    public void addEdge(Exp start, Exp end) {
        if (!pointerFlowGraph.hasEdge(start, end)) {
            pointerFlowGraph.addEdge(start, end);
            if (pointsToSet.get(start) != null) {
                workList.offer(new Pair<Exp, HashSet<Integer>>(start, pointsToSet.get(start)));
            }
        }
    }

    public void propagate(Exp n, HashSet<Integer> pts) {
        if (!pts.isEmpty()) {
            pointsToSet.computeIfAbsent(n, k->{new HashSet<Integer>();}).addAll(pts);
            pointerFlowGraph.getSuccsOf(n).forEach(s->{
                workList.offer(new Pair<Exp, HashSet<Integer>>(s, pointsToSet.get(pts)));
            });
        }
    }
}
