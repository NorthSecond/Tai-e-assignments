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
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.Comparator;
import java.util.Queue;
import java.util.Set;
import java.util.TreeSet;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        // 常量传播的结果
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        // 活跃变量分析的结果
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        // iterate over all statements in the CFG
        Set<Stmt> liveCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        // BFS 获得所有的活跃代码
        Queue<Stmt> queue = new java.util.LinkedList<>();
        queue.add(cfg.getEntry());
        Stmt now;
        while (!queue.isEmpty()) {
            now = queue.poll();
            // 将now加入活跃代码
            if (!liveCode.add(now)) {
                continue;
            }
            // Assignment
            // 这里直接用now会报错
            if(now instanceof AssignStmt<?,?> ass && ass.getLValue() instanceof Var v) {
                // 加入副作用检查
                if (!liveVars.getResult(now).contains(v) && hasNoSideEffect(ass.getRValue())) {
                    // WA：这个情况下，这个赋值语句是死代码
                    liveCode.remove(now);
                }
                queue.addAll(cfg.getSuccsOf(now));
            }
            // If 语句
            else if(now instanceof If c) {
                Value cond = ConstantPropagation.evaluate(c.getCondition(), constants.getInFact(c));
                if (cond.isConstant()) {
                    // 如果是常量 加入常量对应的分支
                    for (Edge<Stmt> e : cfg.getOutEdgesOf(c)) {
                        // 转换成int了
                        if ((cond.getConstant() == 1 && e.getKind() == Edge.Kind.IF_TRUE) ||
                                (cond.getConstant() == 0 && e.getKind() == Edge.Kind.IF_FALSE)) {
                            queue.add(e.getTarget());
                        }
                    }
                } else {
                    // 如果不是常量 加入两个分支
                    queue.addAll(cfg.getSuccsOf(c));
                }
            }
            // Switch
            else if(now instanceof SwitchStmt sw) {
                Value cond = ConstantPropagation.evaluate(sw.getVar(), constants.getInFact(sw));
                if(cond.isConstant()) {
                    // 遍历判断能不能命中
                    boolean flag = false;
                    for(Pair<Integer, Stmt> e : sw.getCaseTargets()){
                        if(e.first() == cond.getConstant()) {
                            // 中了
                            flag  = true;
                            queue.add(e.second());
                        }
                    }
                    if(!flag) {
                        // 没中
                        queue.add(sw.getDefaultTarget());
                    }
                } else {
                    // 不是常量 加入所有的分支
                    queue.addAll(cfg.getSuccsOf(sw));
                }
            }else{
                // 啥情况都不是 直接加罢
                queue.addAll(cfg.getSuccsOf(now));
            }
        }
        for(Stmt s : cfg.getNodes()) {
            if(!liveCode.contains(s)) {
                deadCode.add(s);
            }
        }
        deadCode.remove(cfg.getExit());
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
