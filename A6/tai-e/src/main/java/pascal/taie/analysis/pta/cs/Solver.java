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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (!callGraph.contains(csMethod)){
            addReachable(csMethod);
            csMethod.getMethod().getIR().getStmts().forEach(stmt -> stmt.accept(new StmtProcessor(csMethod)));
        }

    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }


        @Override
        public Void visit(New stmt) {
            Pointer node = csManager.getCSVar(context, stmt.getLValue());
            Obj new_obj = heapModel.getObj(stmt);
            Context obj_context = contextSelector.selectHeapContext(csMethod, new_obj);
            var new_obj_ctx = csManager.getCSObj(obj_context, new_obj);
            PointsToSet pts = PointsToSetFactory.make(new_obj_ctx);
            workList.addEntry(node, pts);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getCSVar(context, stmt.getLValue())
            );
            return StmtVisitor.super.visit(stmt);
        }


        @Override
        public Void visit(Invoke stmt){
            //We can only deal with static method in
            if (stmt.isStatic()){
                var callee = resolveCallee(null, stmt);
                var csCallSite = csManager.getCSCallSite(context, stmt);
                var ct = contextSelector.selectContext(csCallSite, callee);
                var csCallee = csManager.getCSMethod(ct, callee);
                processCallAndRet(csCallSite, csCallee);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()){
                addPFGEdge(
                        csManager.getStaticField(stmt.getFieldRef().resolve()),
                            csManager.getCSVar(context, stmt.getLValue())
                );
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()){
                addPFGEdge(
                        csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return StmtVisitor.super.visit(stmt);
        }
    }

    private  void processCallAndRet(CSCallSite csCallsite, CSMethod callee){
        if (!callGraph.getCalleesOf(csCallsite).contains(callee)){
            CallKind callkind = null;
            var callSite = csCallsite.getCallSite();
            if (callSite.isSpecial()) callkind = CallKind.SPECIAL;
            if (callSite.isVirtual()) callkind = CallKind.VIRTUAL;
            if (callSite.isInterface()) callkind = CallKind.INTERFACE;
            if (callSite.isSpecial()) callkind = CallKind.STATIC;
            if(callkind != null){
                callGraph.addEdge(new Edge<>(callkind, csCallsite, callee));
                addReachable(callee);
                var params = callee.getMethod().getIR().getParams();
                var args = callSite.getRValue().getArgs();
                assert  params.size() == args.size();
                var c = csCallsite.getContext();
                var ct = callee.getContext();
                for(int i = 0; i < params.size(); i++){
                    addPFGEdge(csManager.getCSVar(c, args.get(i)),
                            csManager.getCSVar(ct, params.get(i))
                            );
                }
                if (callSite.getLValue() != null){
                    var ret = callSite.getLValue();
                    for(var fret: callee.getMethod().getIR().getReturnVars()){
                        addPFGEdge(
                                csManager.getCSVar(ct, fret),
                                csManager.getCSVar(c, ret)
                        );
                    }

                }
            }
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
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
            if (entry.pointer() instanceof CSVar varPtr){
                var x = varPtr.getVar();
                var ctx = varPtr.getContext();
                for(var o: delta){
                    //load
                    x.getLoadFields().forEach(loadstmt -> {
                        addPFGEdge(
                                        csManager.getInstanceField(o, loadstmt.getFieldAccess().getFieldRef().resolve()),
                                        csManager.getCSVar(ctx, loadstmt.getLValue())
                                );
                    });
                    //store
                    x.getStoreFields().forEach(storestmt -> {
                        addPFGEdge(
                           csManager.getCSVar(ctx, storestmt.getRValue()),
                           csManager.getInstanceField(o, storestmt.getFieldAccess().getFieldRef().resolve())
                        );
                    });
                    //load array
                    x.getLoadArrays().forEach(loadArray -> {
                                addPFGEdge(
                                        csManager.getArrayIndex(o),
                                        csManager.getCSVar(ctx, loadArray.getLValue())
                                );

                    });
                    //store array
                    x.getStoreArrays().forEach(storeArray -> {
                      addPFGEdge(
                              csManager.getCSVar(ctx, storeArray.getRValue()),
                              csManager.getArrayIndex(o)
                      );
                    });
                    //process call
                    processCall(varPtr, o);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var delta = PointsToSetFactory.make();
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        recv.getVar().getInvokes().forEach(
                callSite -> {
                    var csCallSite = csManager.getCSCallSite(recv.getContext(), callSite);
                    var callee = resolveCallee(recvObj, callSite);
                    var csCallee = csManager.getCSMethod(contextSelector.selectContext(csCallSite, recvObj, callee), callee);
                    workList.addEntry(
                            csManager.getCSVar(csCallee.getContext(), callee.getIR().getThis()),
                            PointsToSetFactory.make(recvObj)
                    );
                    processCallAndRet(csCallSite, csCallee);
                }
        );
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
