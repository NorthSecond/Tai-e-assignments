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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        // 除了前三行的后面的部分
        // Worklist ← all basic blocks
        LinkedList<Node> worklist = new LinkedList<>(cfg.getNodes());
        // while Worklist is not empty
        while (!worklist.isEmpty()) {
            // Pick a basic block B from Worklist
            Node b = worklist.poll();
            // Old_OUT = OUT[B]
            CPFact out = null;
            if(result.getOutFact(b) instanceof CPFact fact){
//                System.out.println("Old_OUT = OUT[B] = " + fact);
                out = fact;
            }
//            CPFact out = (CPFact) result.getOutFact(b);
            // IN[B] = ⊔P a predecessor of B OUT[P];
            CPFact in = new CPFact();
            for (Node pred : cfg.getPredsOf(b)) {
                analysis.meetInto(result.getOutFact(pred), (Fact)in);
            }
            // OUT[B] = gen B U (IN[B] - kill B);
            if(analysis.transferNode(b, (Fact) in, (Fact)out)){
                // if (old_OUT ≠ OUT[B]):Add all successors of B to Worklist
                worklist.addAll(cfg.getSuccsOf(b));
            }
            result.setInFact(b, (Fact) in);
            result.setOutFact(b, (Fact) out);
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
