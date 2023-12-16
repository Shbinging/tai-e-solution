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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.util.collection.Pair;

import java.util.LinkedList;
import java.util.Queue;

import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.*;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        icfg.getNodes().forEach(node -> {result.setOutFact(node, analysis.newInitialFact());});
        icfg.entryMethods().forEach(method -> {result.setOutFact(icfg.getEntryOf(method), analysis.newBoundaryFact(icfg.getEntryOf(method)));});
    }

    private void doStore(Stmt stmt, CPFact in){
        if (stmt instanceof StoreField store_stmt){
            if (!ConstantPropagation.canHoldInt(store_stmt.getRValue())) return;
            if (store_stmt.getFieldAccess() instanceof InstanceFieldAccess access){
                for(var obj: pta.getPointsToSet(access.getBase())){
                    var key = new Pair<>(obj, access.getFieldRef());
                    var in_val = objFiledToVal.getOrDefault(key, Value.getUndef());
                    var out_val = ConstantPropagation.meetValue(ConstantPropagation.evaluate(store_stmt.getRValue(), in), in_val);
                    if (!out_val.equals(in_val)){
                        //update worklist
                        objFiledToVal.put(key, out_val);
                        for(var alia_v: aliaVars.get(obj)){
                            for(var loadstmt: alia_v.getLoadFields()){
                                if (loadstmt.getFieldAccess().getFieldRef().equals(access.getFieldRef())){
                                    workList.add((Node) loadstmt);
                                }
                            }
                        }
                    }
                }
            }else if (store_stmt.getFieldAccess() instanceof StaticFieldAccess access){
                var key = new Pair<>(access.getFieldRef().getDeclaringClass(), access.getFieldRef());
                var in_val = objFiledToVal.getOrDefault(key, Value.getUndef());
                var out_val = ConstantPropagation.meetValue(ConstantPropagation.evaluate(store_stmt.getRValue(), in), in_val);
                if (!out_val.equals(in_val)){
                    //update worklist
                    objFiledToVal.put(key, out_val);
                    if (staticFields.containsKey(key)){
                        for(var loadstmt: staticFields.get(key)){
                            workList.add((Node) loadstmt);
                        }
                    }
                }
            }
        }
        if (stmt instanceof StoreArray store_array){
            if (!ConstantPropagation.canHoldInt(store_array.getRValue())) return;
            var index = ConstantPropagation.evaluate(store_array.getArrayAccess().getIndex(), in);
            if (index.isUndef()) return;
            var base = store_array.getArrayAccess().getBase();
            for(var obj: pta.getPointsToSet(base)){
                var key = new Pair<>(obj, index);
                var in_val = objFiledToVal.getOrDefault(key, Value.getUndef());
                var out_val = ConstantPropagation.meetValue(ConstantPropagation.evaluate(store_array.getRValue(), in), in_val);
                if (!out_val.equals(in_val)){
                    objFiledToVal.put(key, out_val);
                    //we may add some array store which not need to update
                    for(var alias_v: aliaVars.get(obj)){
                        alias_v.getLoadArrays().forEach(loadstmt-> {
                            workList.add((Node) loadstmt);
                        });
                    }
                }
            }
        }
    }

    private void doSolve() {
        Queue<Node> wl = new LinkedList<>(icfg.getNodes());
        workList = wl;
        while(!wl.isEmpty()){
            var b = wl.poll();
            var in = analysis.newInitialFact();
            icfg.getInEdgesOf(b).forEach(edge -> {
                analysis.meetInto(analysis.transferEdge(edge, result.getOutFact(edge.getSource())), in);
            });
            //This is for x = ....
            result.setInFact(b, in);
            if (analysis.transferNode(b, in, result.getOutFact(b))){
                wl.addAll(icfg.getSuccsOf(b));
            }
            //This is for x.x = ...
            doStore((Stmt) b, (CPFact) in);
        }
//        for (var node: icfg.getNodes()){
//            System.out.printf("%s %s\n", node.toString(), result.getResult((Stmt) node));
//        }
    }
}
