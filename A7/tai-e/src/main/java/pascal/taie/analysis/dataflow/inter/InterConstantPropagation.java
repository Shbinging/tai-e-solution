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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Pair;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    public static final Map<Obj, Set<Var>> aliaVars = new HashMap<>();
    public static final Map<Pair<?, ?>, Value> objFiledToVal = new HashMap<>();
    public static final Map<Pair<JClass, FieldRef>, Set<LoadField>> staticFields = new HashMap<>();

    public static PointerAnalysisResult pta;
    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
        for(var ptr_v: pta.getVars()){
            pta.getPointsToSet(ptr_v).forEach(obj -> {
                if (!aliaVars.containsKey(obj)) aliaVars.put(obj, new HashSet<>());
                aliaVars.get(obj).add(ptr_v);
            });
        }
        for(var stmt: icfg.getNodes()){
            if(stmt instanceof LoadField s && s.getFieldAccess() instanceof StaticFieldAccess access){
                var key = new Pair<>(access.getFieldRef().getDeclaringClass(), access.getFieldRef());
                if (!staticFields.containsKey(key)){
                    staticFields.put(key, new HashSet<>());
                }
                staticFields.get(key).add(s);
            }
        }
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        CPFact fact = new CPFact();
        fact.copyFrom(out);
        if (edge.getSource().getDef().isPresent()) {
            Var lvar = (Var) edge.getSource().getDef().get();
            fact.remove(lvar);
        }
        return fact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        InvokeExp exp = ((Invoke) edge.getSource()).getInvokeExp();
        var callee = edge.getCallee().getIR();
        assert exp.getArgCount() == callee.getParams().size();
        CPFact fact = new CPFact();
        for(int i = 0; i < exp.getArgCount(); i++){
            fact.update(callee.getParam(i), callSiteOut.get(exp.getArg(i)));
        }
        return fact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        CPFact fact = new CPFact();
        if (edge.getCallSite().getDef().isPresent()) {
            Var lvar = (Var) edge.getCallSite().getDef().get();
            for (var return_var : edge.getReturnVars()) {
                fact.update(lvar, cp.meetValue(fact.get(lvar), returnOut.get(return_var)));
            }
        }
        return fact;
    }
}
