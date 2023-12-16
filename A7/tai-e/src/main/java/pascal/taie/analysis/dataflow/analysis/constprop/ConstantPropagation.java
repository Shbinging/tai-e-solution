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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.util.collection.Pair;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.pta;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.objFiledToVal;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        var cp_fact = new CPFact();
        cfg.getIR().getParams().forEach(
                param -> {
                    if (canHoldInt(param)){
                        cp_fact.update(param, Value.getNAC());
                    }
                }
        );
        return cp_fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((var, value)->{
            target.update(var, meetValue(value, target.get(var)));
        });
    }

    /**
     * Meets two Values.
     */
    public static Value meetValue(Value v1, Value v2) {
        if (v1.isUndef()) return v2;
        if (v2.isUndef()) return v1;
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        if (v1.getConstant() == v2.getConstant()) return v1;
        else return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        var change = out.copyFrom(in);
        if (stmt instanceof DefinitionStmt<?,?> d_stmt) {
            if (d_stmt.getLValue() instanceof Var v && d_stmt.getRValue() instanceof Exp){
                var e = (Exp) d_stmt.getRValue();
                if (canHoldInt(v)){
                    change |= out.update(v, evaluate(e, in));
                }
            }
        }
        return change;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }




    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var v){
            return in.get(v);
        }
        if (exp instanceof IntLiteral){
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        if (exp instanceof ArithmeticExp ae){
            var op1 = evaluate(ae.getOperand1(), in);
            var op2 = evaluate(ae.getOperand2(), in);
            if (op2.isConstant() && op2.getConstant() == 0){
                if (ae.getOperator() == ArithmeticExp.Op.DIV || ae.getOperator() == ArithmeticExp.Op.REM){
                    return Value.getUndef();
                }
            }
            if (op1.isNAC() || op2.isNAC()) return Value.getNAC();
            if (op1.isUndef() || op2.isUndef()) return Value.getUndef();
            switch (ae.getOperator()){
                case ADD -> {return Value.makeConstant(op1.getConstant() + op2.getConstant());}
                case SUB -> {return Value.makeConstant(op1.getConstant() - op2.getConstant());}
                case MUL -> {return Value.makeConstant(op1.getConstant() * op2.getConstant());}
                case DIV -> {if (op2.getConstant() == 0) return Value.getUndef(); else return Value.makeConstant(op1.getConstant() / op2.getConstant());}
                case REM -> {if (op2.getConstant() == 0) return Value.getUndef(); else return Value.makeConstant(op1.getConstant() % op2.getConstant());}
            }
        }else if (exp instanceof  ConditionExp ce){
            var op1 = evaluate(ce.getOperand1(), in);
            var op2 = evaluate(ce.getOperand2(), in);
            if (op1.isNAC() || op2.isNAC()) return Value.getNAC();
            if (op1.isUndef() || op2.isUndef()) return Value.getUndef();
            switch(ce.getOperator()){
                case EQ -> {return (Value.makeConstant(op1.getConstant() == op2.getConstant() ? 1 : 0));}
                case NE -> {return (Value.makeConstant(op1.getConstant() != op2.getConstant() ? 1 : 0));}
                case GE -> {return (Value.makeConstant(op1.getConstant() >= op2.getConstant() ? 1 : 0));}
                case GT -> {return (Value.makeConstant(op1.getConstant() > op2.getConstant() ? 1 : 0));}
                case LE -> {return (Value.makeConstant(op1.getConstant() <= op2.getConstant() ? 1 : 0));}
                case LT -> {return (Value.makeConstant(op1.getConstant() < op2.getConstant() ? 1 : 0));}
            }
        }else if (exp instanceof ShiftExp se){
            var op1 = evaluate(se.getOperand1(), in);
            var op2 = evaluate(se.getOperand2(), in);
            if (op1.isNAC() || op2.isNAC()) return Value.getNAC();
            if (op1.isUndef() || op2.isUndef()) return Value.getUndef();
            switch (se.getOperator()){
                case SHL -> {return Value.makeConstant(op1.getConstant() << op2.getConstant());}
                case SHR -> {return Value.makeConstant(op1.getConstant() >> op2.getConstant());}
                case USHR ->{return Value.makeConstant(op1.getConstant() >>> op2.getConstant());}
            }
        }else if (exp instanceof  BitwiseExp be){
            var op1 = evaluate(be.getOperand1(), in);
            var op2 = evaluate(be.getOperand2(), in);
            if (op1.isNAC() || op2.isNAC()) return Value.getNAC();
            if (op1.isUndef() || op2.isUndef()) return Value.getUndef();
            switch (be.getOperator()){
                case OR -> {return Value.makeConstant(op1.getConstant() | op2.getConstant());}
                case AND -> {return Value.makeConstant(op1.getConstant() & op2.getConstant());}
                case XOR -> {return Value.makeConstant(op1.getConstant() ^ op2.getConstant());}
            }
        }else if (exp instanceof InstanceFieldAccess access){
            var val = Value.getUndef();
            for (var obj: pta.getPointsToSet(access.getBase())){
                val = meetValue(val, objFiledToVal.getOrDefault(new Pair<>(obj, access.getFieldRef()), Value.getUndef()));
            }
            return val;
        }else if (exp instanceof StaticFieldAccess access){
            return objFiledToVal.getOrDefault(new Pair<>(access.getFieldRef().getDeclaringClass(), access.getFieldRef()), Value.getUndef());
        }else if (exp instanceof ArrayAccess access){
            var idx = evaluate(access.getIndex(), in);
            var val = Value.getUndef();
            if (idx.isConstant()){
                for(var obj: pta.getPointsToSet(access.getBase())){
                    val = meetValue(val, objFiledToVal.getOrDefault(new Pair<>(obj, idx), Value.getUndef()));
                    val = meetValue(val , objFiledToVal.getOrDefault(new Pair<>(obj, Value.getNAC()), Value.getUndef()));
                }
            }else if (idx.isNAC()){
                for(var obj: pta.getPointsToSet(access.getBase())){
                    for(var entry: objFiledToVal.entrySet()){
                        if (entry.getKey().first() == obj && entry.getKey().second() instanceof Value v){
                            if (!v.isNAC()){
                                val = meetValue(val, entry.getValue());
                            }
                        }
                    }
                }
            }else if (idx.isUndef()){
                val = Value.getUndef();
            }
            return val;
        }
        return Value.getNAC();
    }

}
