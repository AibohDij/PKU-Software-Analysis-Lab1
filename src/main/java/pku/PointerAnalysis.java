package pku;

import java.io.*;
import java.lang.reflect.Field;
import java.util.HashMap;
import java.util.HashSet;
import java.util.TreeSet;
import java.util.Queue;
import java.util.Set;
import java.util.List;
import java.util.LinkedList;

import javax.script.SimpleBindings;

import pascal.taie.language.type.Type;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.JClass;


import pascal.taie.util.graph.Edge;
import pascal.taie.util.graph.Graph;
import pascal.taie.util.graph.SimpleGraph;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import pascal.taie.World;
import pascal.taie.analysis.ProgramAnalysis;
import pascal.taie.config.AnalysisConfig;

import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.InvokeSpecial;
import pascal.taie.ir.exp.InvokeInterface;
import pascal.taie.ir.exp.InvokeVirtual;
import pascal.taie.ir.exp.InvokeStatic;
import pascal.taie.ir.exp.CastExp;

import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Cast;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.FieldStmt;

import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.proginfo.MethodRef;

class Obj {
    private final int id;
    private final New allocStmt;
    private final Type type;

    Obj(int id, New allocStmt) {
        this.id = id;
        this.allocStmt = allocStmt;
        this.type = allocStmt.getLValue().getType();
    }

    public int getId() {
        return this.id;
    }

    public New getAllocStmt() {
        return this.allocStmt;
    }

    public Type getType() {
        return this.type;
    }
}

class ObjField {
    private final Obj obj;
    private final FieldRef fieldRef;

    ObjField(Obj obj, FieldRef fieldRef) {
        this.obj = obj;
        this.fieldRef = fieldRef;
    }

    public Obj getObj() {
        return this.obj;
    }

    public FieldRef getFieldRef() {
        return this.fieldRef;
    }

    public String getName() {
        return "o" + ((Integer) this.obj.getId()).toString() + "." + this.fieldRef.getName();
    }
}

class StaticField {
    private final FieldRef fieldRef;

    StaticField(FieldRef fieldRef) {
        this.fieldRef = fieldRef;
    }
    
    public FieldRef getFieldRef() {
        return this.fieldRef;
    }

    public String getName() {
        return this.fieldRef.getName();
    }
}

class ObjArray {
    private final Obj obj;

    ObjArray(Obj obj) {
        this.obj = obj;
    }

    public Obj getObj() {
        return this.obj;
    }

    public String getName() {
        return "o" + ((Integer) this.obj.getId()).toString() + "[*]";
    }
}

class Pointer {
    private Object content;

    Pointer(Var var) {
        this.content = var;
    }

    Pointer(ObjField objField) {
        this.content = objField;
    }

    Pointer(StaticField staticField) {
        this.content = staticField;
    }

    Pointer(ObjArray objArray) {
        this.content = objArray;
    }

    public boolean isVar() {
        return content instanceof Var;
    }

    public boolean isObjField() {
        return content instanceof ObjField;
    }

    public boolean isStaticField() {
        return content instanceof StaticField;
    }

    public boolean isObjArray() {
        return content instanceof ObjArray;
    }

    public Var getAsVar() {
        if (content instanceof Var) {
            return ((Var) content);
        }
        return null;
    }

    public ObjField getAsObjField() {
        if (content instanceof ObjField) {
            return ((ObjField) content);
        }
        return null;
    }

    public StaticField getAsStaticField() {
        if (content instanceof StaticField) {
            return ((StaticField) content);
        }
        return null;
    }

    public ObjArray getAsObjArray() {
        if (content instanceof ObjArray) {
            return ((ObjArray) content);
        }
        return null;
    }

    public String getName() {
        if (content instanceof Var) {
            return ((Var) content).getName();
        } else if (content instanceof ObjField) {
            return ((ObjField) content).getName();
        } else if (content instanceof StaticField) {
            return ((StaticField) content).getName();
        } else if (content instanceof ObjArray){
            return ((ObjArray) content).getName();
        } else {
            return null;
        }
    }
}
public class PointerAnalysis extends PointerAnalysisTrivial
{
    public static final String ID = "pku-pta";

    public record Entry(Pointer ptr, HashSet<Obj> pts) { }

    public SimpleGraph<Pointer> pointerFlowGraph;
    //public SimpleGraph<JMethod> callGraph;
    public HashMap<Invoke, HashSet<JMethod>> callGraph;
    public Queue<Entry> workList;
    public HashSet<JMethod> reachableMethods;
    public HashSet<Stmt> reachableStatements;
    public HashMap<Pointer, HashSet<Obj>> pointsToSet;

    public HashMap<New, Obj> objManager;
    public HashMap<Obj, New> reverseMap;
    public HashMap<Obj, HashMap<FieldRef, ObjField>> objFieldManager;
    public HashMap<StaticFieldAccess, StaticField> staticFieldManager;
    public HashMap<Obj, ObjArray> objArrayManager;

    public HashMap<Var, Pointer> varPointerManager;
    public HashMap<ObjField, Pointer> objFieldPointerManager;
    public HashMap<StaticField, Pointer> staticFieldPointerManager;
    public HashMap<ObjArray, Pointer> objArrayPointerManager;

    public static int objCnt = 0;
    

    public PointerAnalysis(AnalysisConfig config) {
        super(config);
        pointerFlowGraph = new SimpleGraph<>();
        callGraph = new HashMap<>();
        workList = new LinkedList<>();
        reachableMethods = new HashSet<>();
        reachableStatements = new HashSet<>();
        pointsToSet = new HashMap<>();

        objManager = new HashMap<>();
        reverseMap = new HashMap<>();
        objFieldManager = new HashMap<>();
        staticFieldManager = new HashMap<>();
        objArrayManager = new HashMap<>();

        varPointerManager = new HashMap<>();
        objFieldPointerManager = new HashMap<>();
        staticFieldPointerManager = new HashMap<>();
        objArrayPointerManager = new HashMap<>();
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
    
        addReachable(main);
        while (!workList.isEmpty()) {
            Entry entry = workList.poll();
            Pointer n = entry.ptr();
            HashSet<Obj> delta = new HashSet<>(entry.pts());
            logger.info("Working with {}", n.getName());
            if (pointsToSet.get(n) != null) {
                delta.removeAll(pointsToSet.get(n));
            }
            if (!delta.isEmpty()) {
                propagate(n, delta);
                if (n.isVar()) {
                    Var x = n.getAsVar();
                    delta.forEach(obj->{
                        reachableStatements.forEach(stmt->{
                            if (stmt instanceof FieldStmt<?, ?>) {
                                if (stmt instanceof StoreField) {
                                    // x.f = y
                                    RValue rval = ((StoreField) stmt).getRValue();
                                    FieldAccess lval = ((StoreField) stmt).getFieldAccess();
                                    if (lval instanceof InstanceFieldAccess) {
                                        if (((InstanceFieldAccess) lval).getBase() == x) {
                                            FieldRef field = lval.getFieldRef();
                                            ObjField objField = getObjField(obj, field);
                                            if (rval instanceof Var) {
                                                addEdge(getPointer(((Var) rval)), getPointer(objField));
                                            }
                                        }
                                    }
                                } else if (stmt instanceof LoadField) {
                                    // y = x.f
                                    LValue lval = ((LoadField) stmt).getLValue();
                                    FieldAccess rval = ((LoadField) stmt).getFieldAccess();
                                    if (rval instanceof InstanceFieldAccess) {
                                        if (((InstanceFieldAccess) rval).getBase() == x) {
                                            FieldRef field = rval.getFieldRef();
                                            ObjField objField = getObjField(obj, field);
                                            if (lval instanceof Var) {
                                                addEdge(getPointer(objField), getPointer(((Var) lval)));
                                            }
                                        }
                                    }
                                } 
                            } else if (stmt instanceof StoreArray) {
                                // x[i] = y
                                RValue rval = ((StoreArray) stmt).getRValue();
                                ArrayAccess lval = ((StoreArray) stmt).getArrayAccess();
                                if (lval.getBase() == x) {
                                    ObjArray objArray = getObjArray(obj);
                                    if (rval instanceof Var) {
                                        addEdge(getPointer(((Var) rval)), getPointer(objArray));
                                    }
                                }
                            } else if (stmt instanceof LoadArray) {
                                // y = x[i]
                                LValue lval = ((StoreArray) stmt).getLValue();
                                ArrayAccess rval = ((StoreArray) stmt).getArrayAccess();
                                if (rval.getBase() == x) {
                                    ObjArray objArray = getObjArray(obj);
                                    if (lval instanceof Var) {
                                        addEdge(getPointer(objArray), getPointer(((Var) lval)));
                                    }
                                }
                            }
                        });
                        processCall(x, obj);
                    });
                }
            }
        }

        jclass.getDeclaredMethods().forEach(method->{
            if(!method.isAbstract())
                preprocess.analysis(method.getIR());            
        });
        preprocess.test_pts.forEach((test_id, pt)->{
            HashSet<Obj> pts = pointsToSet.get(getPointer(pt));
            if (pts.isEmpty()) {
                logger.info("Empty for {}", pt.getName());
            }
            TreeSet<Integer> objs = new TreeSet<>();
            pts.forEach(obj->{
                New stmt = reverseMap.get(obj);
                if (preprocess.obj_ids.get(stmt) != null) {
                    objs.add(preprocess.obj_ids.get(stmt));
                }
                
            });
            result.put(test_id, objs);
        });

        dump(result);
        return result;
    }

    public void addReachable(JMethod method)
    {
        logger.info("Processing with method {}", method.getName());
        //PreprocessResult preprocess = method.getIR().getResult("pku-pta-preprocess"); // Preprocess the method

        if (!reachableMethods.contains(method)) {
            reachableMethods.add(method);
            var stmts = method.getIR().getStmts();
            stmts.forEach(stmt->{
                if (!reachableStatements.contains(stmt)) {
                    reachableStatements.add(stmt);
                }
                if (stmt instanceof AssignStmt<?, ?>) {
                    if (stmt instanceof New) {
                        LValue lval = ((New) stmt).getLValue();
                        int obj_id = objCnt;
                        objCnt += 1;
                        logger.info("Adding object {} to the object list", obj_id);
                        Obj obj = new Obj(obj_id, ((New) stmt));
                        objManager.put(((New) stmt), obj);
                        reverseMap.put(obj, ((New) stmt));
                        HashSet<Obj> pts = new HashSet<>();
                        pts.add(obj);
                        if (lval instanceof Var) {
                            workList.offer(new Entry(getPointer(((Var) lval)), pts));
                        }
                    } else if (stmt instanceof Copy) {
                        LValue lval = ((Copy) stmt).getLValue();
                        RValue rval = ((Copy) stmt).getRValue();
                        if ((lval instanceof Var) && (rval instanceof Var)) {
                            addEdge(getPointer(((Var) rval)), getPointer(((Var) lval)));
                        }
                    } else if (stmt instanceof Cast) {
                        LValue lval = ((Cast) stmt).getLValue();
                        CastExp castExp = ((Cast) stmt).getRValue();
                        Var rval = castExp.getValue();
                        if (lval instanceof Var) {
                            addEdge(getPointer(rval), getPointer(((Var) lval)));
                        }
                    } else if (stmt instanceof StoreField) {
                        RValue rval = ((StoreField) stmt).getRValue();
                        FieldAccess lval = ((StoreField) stmt).getFieldAccess();
                        if (lval instanceof StaticFieldAccess) {
                            StaticField staticField = getStaticField(((StaticFieldAccess) lval));
                            if (rval instanceof Var) {
                                addEdge(getPointer(((Var) rval)), getPointer(staticField));
                            }
                        }
                    } else if (stmt instanceof LoadField) {
                        LValue lval = ((LoadField) stmt).getLValue();
                        FieldAccess rval = ((LoadField) stmt).getFieldAccess();
                        if (rval instanceof StaticFieldAccess) {
                            StaticField staticField = getStaticField(((StaticFieldAccess) rval));
                            if (lval instanceof Var) {
                                addEdge(getPointer(staticField), getPointer(((Var) lval)));
                            }                            
                        }
                    }
                } else if(stmt instanceof Invoke) {
                    if (((Invoke) stmt).getInvokeExp() instanceof InvokeStatic) {
                        InvokeStatic invokeExp = (InvokeStatic) ((Invoke) stmt).getInvokeExp();
                        JMethod targetMethod = invokeExp.getMethodRef().resolve();
                        
                        HashSet<JMethod> innerSet = callGraph.get(((Invoke) stmt));
                        if (innerSet == null) {
                            innerSet = new HashSet<JMethod>();
                            callGraph.put(((Invoke) stmt), innerSet);
                        }
                        if (!innerSet.contains(targetMethod)) {
                            innerSet.add(targetMethod);
                            addReachable(targetMethod);

                            List<Var> params = targetMethod.getIR().getParams();
                            List<Var> args = invokeExp.getArgs();
                            for (int i = 0; i < params.size() && i < args.size(); i++) {
                                addEdge(getPointer(args.get(i)), getPointer(params.get(i)));
                            }

                            List<Var> returnVarList = targetMethod.getIR().getReturnVars();
                            if (!returnVarList.isEmpty()) {
                                Var returnVar = returnVarList.get(0);
                                LValue lval = ((Invoke) stmt).getLValue();
                                if (lval instanceof Var) {
                                    addEdge(getPointer(returnVar), getPointer(((Var) lval)));
                                }
                            }
                        }
                    }
                }
            });
        }
    }

    public void processCall(Var x, Obj obj) {
        HashSet<Invoke> iterStatements= new HashSet<>(); 
        reachableStatements.forEach(stmt->{
            if (stmt instanceof Invoke) {
                if (((Invoke) stmt).getInvokeExp() instanceof InvokeInstanceExp) {
                    InvokeInstanceExp invokeExp = (InvokeInstanceExp) ((Invoke) stmt).getInvokeExp();
                    if (invokeExp.getBase() == x) {
                        iterStatements.add(((Invoke) stmt));
                    }
                }
            }
        });        
        iterStatements.forEach(stmt->{
            InvokeInstanceExp invokeExp = ((InvokeInstanceExp) stmt.getInvokeExp());
            JMethod targetMethod = Dispatch(obj, invokeExp.getMethodRef());
            logger.info("Target method is {}", targetMethod.getName());
            HashSet<Obj> pts = new HashSet<>();
            pts.add(obj);
            workList.offer(new Entry(getPointer(targetMethod.getIR().getThis()), pts));

            HashSet<JMethod> innerSet = callGraph.get(stmt);
            if (innerSet == null) {
                innerSet = new HashSet<JMethod>();
                callGraph.put(stmt, innerSet);
            }
            if (!innerSet.contains(targetMethod)) {
                innerSet.add(targetMethod);
                addReachable(targetMethod);

                List<Var> params = targetMethod.getIR().getParams();
                List<Var> args = invokeExp.getArgs();
                for (int i = 0; i < params.size() && i < args.size(); i++) {
                    addEdge(getPointer(args.get(i)), getPointer(params.get(i)));
                }

                List<Var> returnVarList = targetMethod.getIR().getReturnVars();
                if (!returnVarList.isEmpty()) {
                    Var returnVar = returnVarList.get(0);
                    LValue lval = stmt.getLValue();
                    if (lval instanceof Var) {
                        addEdge(getPointer(returnVar), getPointer(((Var) lval)));
                    }
                }
            }
        });
        return;
    }

    public JMethod Dispatch(Obj obj, MethodRef methodRef) {
        Type objType = obj.getType();
        if (objType instanceof ClassType) {
            JClass jclass = World.get().getClassHierarchy().getClass(((ClassType) objType).getName());
            return World.get().getClassHierarchy().dispatch(jclass, methodRef);
        }
        return null;
    }

    public void addEdge(Pointer start, Pointer end) {
        logger.info("Adding edge from {} to {}", start.getName(), end.getName());
        if (!pointerFlowGraph.hasEdge(start, end)) {
            pointerFlowGraph.addEdge(start, end);
            if (pointsToSet.get(start) != null) {
                workList.offer(new Entry(end, new HashSet<>(pointsToSet.get(start))));
            }
        }
    }

    public void propagate(Pointer n, HashSet<Obj> pts) {
        logger.info("Propagating from {}", n.getName());
        if (!pts.isEmpty()) {
            if (pointsToSet.get(n) != null) {
                pointsToSet.get(n).addAll(pts);
            } else {
                pointsToSet.put(n, pts);
            }
            pointerFlowGraph.getSuccsOf(n).forEach(s->{
                logger.info("Propagating to {}", s.getName());
                workList.offer(new Entry(s, pts));
            });
        }
    }

    public ObjField getObjField(Obj obj, FieldRef field) {
        HashMap<FieldRef, ObjField> innerMap = objFieldManager.get(obj);
        if (innerMap == null) {
            innerMap = new HashMap<>();
            objFieldManager.put(obj, innerMap);
        }
        if (objFieldManager.get(obj).get(field) == null) {
            innerMap.put(field, new ObjField(obj, field));
        }
        return objFieldManager.get(obj).get(field);
    }

    public StaticField getStaticField(StaticFieldAccess x) {
        if (staticFieldManager.get(x) == null) {
            staticFieldManager.put(x, new StaticField(x.getFieldRef()));
        }
        return staticFieldManager.get(x);
    }

    public ObjArray getObjArray(Obj obj) {
        if (objArrayManager.get(obj) == null) {
            objArrayManager.put(obj, new ObjArray(obj));
        }
        return objArrayManager.get(obj);
    }

    public Pointer getPointer(Var x) {
        if (varPointerManager.get(x) == null) {
            varPointerManager.put(x, new Pointer(x));
        }
        return varPointerManager.get(x);
    }

    public Pointer getPointer(ObjField x) {
        if (objFieldPointerManager.get(x) == null) {
            objFieldPointerManager.put(x, new Pointer(x));
        }
        return objFieldPointerManager.get(x);
    }

    public Pointer getPointer(StaticField x) {
        if (staticFieldPointerManager.get(x) == null) {
            staticFieldPointerManager.put(x, new Pointer(x));
        }
        return staticFieldPointerManager.get(x);
    }

    public Pointer getPointer(ObjArray x) {
        if (objArrayPointerManager.get(x) == null) {
            objArrayPointerManager.put(x, new Pointer(x));
        }
        return objArrayPointerManager.get(x);
    }
}
