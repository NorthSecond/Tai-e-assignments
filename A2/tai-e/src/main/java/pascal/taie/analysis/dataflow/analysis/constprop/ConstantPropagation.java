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
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import javax.annotation.Nullable;
import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
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
        // DONE - finish me
        if (exp instanceof IntLiteral e) {
            // if x = c gen = {(x, c)}
            return Value.makeConstant(e.getValue());
        } else if (exp instanceof Var v) {
            // if x = y gen = {(x, y)}
            if (in.get(v).isConstant()) {
                return Value.makeConstant(in.get(v).getConstant());
            }
            return in.get(v);
        } else if (exp instanceof BinaryExp b) {
            // if x = y op z gen = {(x, y op z)}
            Value v1 = evaluate(b.getOperand1(), in);
            Value v2 = evaluate(b.getOperand2(), in);
//            if (v1 == null || v2 == null) {
//                return Value.getUndef();
//            }
            // WA:没有考虑除0……
            if (v2.isConstant() && v2.getConstant() == 0
                    && b.getOperator() instanceof ArithmeticExp.Op op) {
                if (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) {
                    return Value.getUndef();
                }

            }
            // WA: NAC 参与计算
            if(v1.isNAC() || v2.isNAC()){
                return Value.getNAC();
            }

            BinaryExp.Op op = b.getOperator();
            if (v1.isConstant() && v2.isConstant()) {
                // if x1, x2 is constant
                if (op instanceof ArithmeticExp.Op aop) {
                    switch (aop) {
                        case ADD -> {
                              return Value.makeConstant(v1.getConstant() + v2.getConstant());
                        }
                        case SUB -> {
                                return Value.makeConstant(v1.getConstant() - v2.getConstant());
                        }
                        case MUL -> {
                                return Value.makeConstant(v1.getConstant() * v2.getConstant());
                        }
                        case DIV -> {
                                return Value.makeConstant(v1.getConstant() / v2.getConstant());
                        }
                        case REM -> { // 差点没看见这玩意
                                return Value.makeConstant(v1.getConstant() % v2.getConstant());
                        }
                        default -> { // should not happen
                            return Value.getNAC();
                        }
                    }
                } else if (op instanceof ConditionExp.Op cop) {
                    switch (cop) {
                        case EQ -> {
                                return Value.makeConstant(v1.getConstant() == v2.getConstant() ? 1 : 0);
                        }
                        case NE -> {
                                return Value.makeConstant(v1.getConstant() == v2.getConstant() ? 0 : 1);
                        }
                        case LT -> {
                                return Value.makeConstant(v1.getConstant() < v2.getConstant() ? 1 : 0);
                        }
                        case GT -> {
                                return Value.makeConstant(v1.getConstant() > v2.getConstant() ? 1 : 0);
                        }
                        case LE -> {
                                return Value.makeConstant(v1.getConstant() <= v2.getConstant() ? 1 : 0);
                        }
                        case GE -> {
                                return Value.makeConstant(v1.getConstant() >= v2.getConstant() ? 1 : 0);
                        }
                        default -> { // should not happen
                            return Value.getNAC();
                        }
                    }
                } else if (op instanceof ShiftExp.Op sop) {
                    switch (sop) {
                        case SHL -> {
                                return Value.makeConstant(v1.getConstant() << v2.getConstant());
                        }
                        case SHR -> {
                                return Value.makeConstant(v1.getConstant() >> v2.getConstant());
                        }
                        case USHR -> {
                                return Value.makeConstant(v1.getConstant() >>> v2.getConstant());
                        }
                        default -> { // should not happen
                            return Value.getNAC();
                        }
                    }
                } else if (op instanceof BitwiseExp.Op bop) {
                    switch (bop) {
                        case OR -> {
                                return Value.makeConstant(v1.getConstant() | v2.getConstant());
                        }
                        case AND -> {
                                return Value.makeConstant(v1.getConstant() & v2.getConstant());
                        }
                        case XOR -> {
                                return Value.makeConstant(v1.getConstant() ^ v2.getConstant());
                        }
                    }
                }
            }
            // UNDEF // otherwise
            return Value.getUndef();
        }
        // should not reach here
        return Value.getNAC();
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // DONE - finish me
        CPFact res = new CPFact();
        List<Var> params = cfg.getIR().getParams();
        for (Var param : params) {
            if (canHoldInt(param)) {
                res.update(param, Value.getNAC());
            }
        }
        return res;
    }

    @Override
    public CPFact newInitialFact() {
        // DONE - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((var, value) -> {
            Value targetValue = meetValue(value, target.get(var));
            target.update(var, targetValue);
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // DONE - finish me
        if (v1.isNAC() || v2.isNAC()) {
            // NAC n v = NAC
            return Value.getNAC();
        } else if (v1.isUndef() && v2.isUndef()) {
            // Undef n Undef = Undef
            return Value.getUndef();
        } else if (v1.isUndef()) {
            // Undef n v = v
            // return v2;
            return Value.makeConstant(v2.getConstant());
        } else if (v2.isUndef()) {
            // v n Undef = v
//            return v1;
            return Value.makeConstant(v1.getConstant());
        } else if (v1.isConstant() && v2.isConstant() && v1.equals(v2)) {
            // v n v = v
            return Value.makeConstant(v1.getConstant());
        } else if (v1.isConstant() && v2.isConstant() && !v1.equals(v2)) {
            // v n w = NAC
            return Value.getNAC();
        } else {
            // should not happen
            return Value.getUndef();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // 长记性了 这次是引用传递了
        boolean changed = false;
        CPFact oldOut = out.copy();
        in.forEach(out::update);
        if(!out.equals(oldOut)){
            changed = true;
        }
        if(stmt instanceof DefinitionStmt<?,?> de &&
                de.getLValue() instanceof Var v && canHoldInt(v)){
            // 更新赋值语句
            Value value = in.get(v);
            Value newValue = evaluate(de.getRValue(), in);
            out.update(v, newValue);
            if(!value.equals(newValue)){
                changed = true;
            }
        }
        return changed;
    }
}
