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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.ir.stmt.If;

import java.util.Comparator;
import java.util.Set;
import java.util.TreeSet;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    Stmt getTypeEdgeDst(Stmt stmt, Edge.Kind kind, CFG<Stmt> cfg){
        for (var next_edge: cfg.getOutEdgesOf(stmt)){
            if (next_edge.getKind() == kind){
                return next_edge.getTarget();
            }
        }
        return null;
    }
    void dfsCfg(Stmt stmt, Set<Stmt> reach_stmts,  CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants, DataflowResult<Stmt, SetFact<Var>> liveVars){
        if (stmt == null){
            return;
        }
        if (reach_stmts.contains(stmt)){
            return;
        }
        reach_stmts.add(stmt);
        if (stmt instanceof If istmt){
            var cond_res = ConstantPropagation.evaluate(istmt.getCondition(), constants.getInFact(stmt));
            if (cond_res.isConstant()){
                Stmt next_stmt = null;
                if (cond_res.getConstant() == 0){
                    next_stmt = getTypeEdgeDst(stmt, Edge.Kind.IF_FALSE, cfg);
                }else{
                    next_stmt = getTypeEdgeDst(stmt, Edge.Kind.IF_TRUE, cfg);
                }
                assert next_stmt != null;
                dfsCfg(next_stmt, reach_stmts, cfg, constants, liveVars);
            }else{
                for(var next_stmt:cfg.getSuccsOf(stmt)){
                    dfsCfg(next_stmt, reach_stmts, cfg, constants, liveVars);
                }
            }
        }else if (stmt instanceof SwitchStmt sstmt){
            var cond_res = ConstantPropagation.evaluate(sstmt.getVar(), constants.getOutFact(stmt));
            if (cond_res.isConstant()){
                var val = cond_res.getConstant();
                boolean match = false;
                for (var p: sstmt.getCaseTargets()){
                    if (val == p.first()){
                        dfsCfg(p.second(), reach_stmts, cfg, constants, liveVars);
                        match = true;
                    }
                }
                if (!match){
                    dfsCfg(sstmt.getDefaultTarget(), reach_stmts, cfg, constants, liveVars);
                }
            }else{
                for(var next_stmt:cfg.getSuccsOf(stmt)){
                    dfsCfg(next_stmt, reach_stmts, cfg, constants, liveVars);
                }
            }
        }else if (stmt instanceof AssignStmt<?,?> astmt){
            if(hasNoSideEffect(astmt.getRValue())){
                if (astmt.getLValue() instanceof Var v){
                    if (!liveVars.getResult(astmt).contains(v)){
                        reach_stmts.remove(astmt);
                    }
                }
            }
            for(var next_stmt:cfg.getSuccsOf(stmt)){
                dfsCfg(next_stmt, reach_stmts, cfg, constants, liveVars);
            }
        }else{
            for(var next_stmt:cfg.getSuccsOf(stmt)){
                dfsCfg(next_stmt,  reach_stmts, cfg, constants, liveVars);
            }
        }
    }


    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);

        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        Set<Stmt> reach_stmts = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        dfsCfg(cfg.getEntry(), reach_stmts, cfg, constants, liveVars);
        for (var stmt: ir.getStmts()){
            if (!reach_stmts.contains(stmt)){
                deadCode.add(stmt);
            }
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
