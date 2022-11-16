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
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.List;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp; // 常量传播的结果

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
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
        // 实质上还是一个常量传播
        // 只不过说分析的对象变成了 ICFG
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // Call Node
        boolean[] changed = new boolean[1];
        in.forEach(((var, value) -> {
            if(out.update(var, value)) {
                changed[0] = true;
            }
        }));
        return changed[0];
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // Non-Call Node 即为没有进行函数调用的节点
        // 直接使用常量传播的结果
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // Normal Edge
        // 不涉及过程间的常量传播
        // transferEdge(edge, fact) = fact
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // Call To Return
        Invoke invoke = (Invoke) edge.getSource();
        Var lv = invoke.getLValue();
        // 把等号左侧的变量和它的值从 fact 中kill 掉
        if(lv != null) {
            CPFact fact = out.copy();
            fact.remove(lv);
            return fact;
        }else{
            // 而对于等号左侧没有变量的调用，比如 m(…)，
            // edge transfer 函数的处理方式与对待 normal edge 的一致
            // 即不涉及过程间的常量传播
            return out;
        }
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // Call Edge
        // 首先从调用点的 OUT fact 中获取实参的值
        // 实参的值
        List<Var> args = edge.getCallee().getIR().getParams();

        // 调用信息
        Invoke invoke = (Invoke) edge.getSource();
        // 调用的方法
        InvokeExp invokeExp = invoke.getInvokeExp();
        List<Var> invokeExpArgs = invokeExp.getArgs();


        // 然后返回一个新的 fact，这个 fact 把形参映射到它对应的实参的值
        CPFact fact = new CPFact();
        for(int i = 0; i < args.size(); i++) {
            Var arg = args.get(i);
            Var invokeExpArg = invokeExpArgs.get(i);
            fact.update(arg, callSiteOut.get(invokeExpArg));
        }
        return fact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // Return Edge
        // 它从被调用方法的 exit 节点的 OUT fact 中获取返回值(可能有多个)
        CPFact fact = new CPFact();
        Invoke invoke = (Invoke) edge.getCallSite();
        Var lv = invoke.getLValue();
        // 然后返回一个将调用点等号左侧的变量映射到返回值的 fact
        if(lv != null) {
            // 多个变量那我就ForEach之
            // 差点忘了这是个常量传播了……
            edge.getReturnVars().forEach(retValue -> fact.update(lv, cp.meetValue(fact.get(lv), returnOut.get(retValue))));
        }
        return fact;
    }
}
