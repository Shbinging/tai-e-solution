/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;
import java.util.stream.Collectors;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (!callGraph.contains(method)){
            callGraph.addReachableMethod(method);
            method.getIR().forEach(x -> x.accept(stmtProcessor));
        }
    }

    private Pointer getVarPtr(Var var){
        return pointerFlowGraph.getVarPtr(var);
    }
    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me


        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()){
                var m = resolveCallee(null, stmt);
                if (!callGraph.getCalleesOf(stmt).contains(m)){
                    callGraph.addEdge(new Edge(CallKind.STATIC, stmt, m));
                    addReachable(m);
                    var params = m.getIR().getParams();
                    var args = stmt.getRValue().getArgs();
                    assert  params.size() == args.size();
                    for(int i = 0; i < params.size(); i++){
                        addPFGEdge(getVarPtr(args.get(i)), getVarPtr(params.get(i)));
                    }
                    if (stmt.getLValue() != null){
                        var ret = stmt.getLValue();
                        for(var fret: resolveCallee(null, stmt).getIR().getReturnVars()){
                            addPFGEdge(getVarPtr(fret), getVarPtr(ret));
                        }
                    }
                }
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(New stmt) {
            workList.addEntry(getVarPtr(stmt.getLValue()), new PointsToSet(heapModel.getObj(stmt)));
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(getVarPtr(stmt.getRValue()), getVarPtr(stmt.getLValue()));
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()){
                addPFGEdge(pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()), getVarPtr(stmt.getLValue()));
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()){
                addPFGEdge(getVarPtr(stmt.getRValue()), pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()));
            }
            return StmtVisitor.super.visit(stmt);
        }

//        @Override
//        public Void visit(LoadArray stmt) {
//            return StmtVisitor.super.visit(stmt);
//        }
//
//        @Override
//        public Void visit(StoreArray stmt) {
//            return StmtVisitor.super.visit(stmt);
//        }


    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)){
            if (!source.getPointsToSet().isEmpty()){
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()){
            var entry = workList.pollEntry();
            var delta = propagate(entry.pointer(), entry.pointsToSet());
            if (entry.pointer() instanceof VarPtr varPtr){
                var x = varPtr.getVar();
                for(var o: delta){
                    //load
                    x.getLoadFields().forEach(loadstmt -> {
                        addPFGEdge(pointerFlowGraph.getInstanceField(o, loadstmt.getFieldRef().resolve()), getVarPtr(loadstmt.getLValue()));
                    });
                    //store
                    x.getStoreFields().forEach(storestmt -> {
                        addPFGEdge(getVarPtr(storestmt.getRValue()), pointerFlowGraph.getInstanceField(o, storestmt.getFieldRef().resolve()));
                    });
                    //load array
                    x.getLoadArrays().forEach(loadArray -> {
                        addPFGEdge(pointerFlowGraph.getArrayIndex(o), getVarPtr(loadArray.getLValue()));
                    });
                    //store array
                    x.getStoreArrays().forEach(storeArray -> {
                        addPFGEdge(getVarPtr(storeArray.getRValue()), pointerFlowGraph.getArrayIndex(o));
                    });
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var delta = new PointsToSet();
        pointsToSet.getObjects().stream().filter(x -> !pointer.getPointsToSet().contains(x)).forEach(delta::addObject);
        if (!delta.isEmpty()){
            delta.objects().forEach(x -> pointer.getPointsToSet().addObject(x));
            for (var s: pointerFlowGraph.getSuccsOf(pointer)){
                workList.addEntry(s, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for(var stmt: var.getInvokes()){
            var m = resolveCallee(recv, stmt);
            if (!callGraph.getCalleesOf(stmt).contains(m)){
                CallKind kind = null;
                if (stmt.isInterface()) kind = CallKind.INTERFACE;
                if (stmt.isVirtual()) kind = CallKind.VIRTUAL;
                if (stmt.isSpecial()) kind = CallKind.SPECIAL;
                if (stmt.isDynamic()) kind = CallKind.DYNAMIC;
                assert kind != null;
                callGraph.addEdge(new Edge(kind, stmt, m));
                addReachable(m);
                var params = m.getIR().getParams();
                var args = stmt.getRValue().getArgs();
                assert  params.size() == args.size();
                for(int i = 0; i < params.size(); i++){
                    addPFGEdge(getVarPtr(args.get(i)), getVarPtr(params.get(i)));
                }
                if (stmt.getLValue() != null){
                    var ret = stmt.getLValue();
                    for(var fret: resolveCallee(null, stmt).getIR().getReturnVars()){
                        addPFGEdge(getVarPtr(fret), getVarPtr(ret));
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
