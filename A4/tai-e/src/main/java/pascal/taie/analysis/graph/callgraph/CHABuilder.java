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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        Queue<JMethod> worklist = new LinkedList<>();
        worklist.add(entry);

        while(!worklist.isEmpty()){
            JMethod method = worklist.poll();

            if(!callGraph.contains(method)) {
                callGraph.addReachableMethod(method);
                // foreach call site cs in m do
                method.getIR().getStmts().stream().filter(stmt -> stmt instanceof Invoke).forEach(cs ->{
                    Set<JMethod> targets = resolve((Invoke) cs);
                    if(((Invoke) cs).isStatic()){
                        targets.forEach(target -> {
                            callGraph.addEdge(new Edge<>(CallKind.STATIC , (Invoke) cs, target));
                            worklist.add(target);
                        });
                    } else if(((Invoke) cs).isSpecial()){
                        targets.forEach(target -> {
                            callGraph.addEdge(new Edge<>(CallKind.SPECIAL , (Invoke) cs, target));
                            worklist.add(target);
                        });
                    } else if(((Invoke) cs).isInterface()){
                        targets.forEach(target -> {
                            callGraph.addEdge(new Edge<>(CallKind.INTERFACE , (Invoke) cs, target));
                            worklist.add(target);
                        });
                    }else if(((Invoke) cs).isVirtual()){
                        targets.forEach(target -> {
                            callGraph.addEdge(new Edge<>(CallKind.VIRTUAL , (Invoke) cs, target));
                            worklist.add(target);
                        });
                    }
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
//        MethodRef methodRef = callSite.getMethodRef();
//        Set<JMethod> result = new HashSet<>();
//        if(callSite.isInterface() || callSite.isVirtual()){
//            JClass rootCls = methodRef.getDeclaringClass();
//            Queue<JClass> queue = new LinkedList<>();
//            queue.add(rootCls);
//            while(!queue.isEmpty()){
//                JClass cls = queue.poll();
//                JMethod dispatchedMethod = dispatch(cls, methodRef.getSubsignature());
//                if(dispatchedMethod != null){
//                    result.add(dispatchedMethod);
//                }
//                if(cls.isInterface()){
//                    queue.addAll(hierarchy.getDirectSubinterfacesOf(cls));
//                    queue.addAll(hierarchy.getDirectImplementorsOf(cls));
//                }else{
//                    queue.addAll(hierarchy.getDirectSubclassesOf(cls));
//                }
//            }
//        }else if(callSite.isSpecial()){
//            JMethod method = dispatch(methodRef.getDeclaringClass(), methodRef.getSubsignature());
//            if(method != null) {
//                result.add(method);
//            }
//        }else if(callSite.isStatic()){
//            result.add(methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature()));
//        }
//        return result;
        MethodRef m = callSite.getMethodRef();
        Set<JMethod> targets =new HashSet<>();

        switch (CallGraphs.getCallKind(callSite)){
            case STATIC -> {
                targets.add(m.getDeclaringClass().getDeclaredMethod(m.getSubsignature()));
            }
            case SPECIAL -> {
                JClass Cm = m.getDeclaringClass();
                if(dispatch(Cm, m.getSubsignature()) != null){
                    targets.add(dispatch(Cm, m.getSubsignature()));
                }
            }
            case INTERFACE -> {
                JClass C = m.getDeclaringClass();
                Queue<JClass> subTypes = new LinkedList<>();
                subTypes.add(C);
                // BFS 遍历类的所有子类
                while(!subTypes.isEmpty()){
                    JClass now = subTypes.poll();
                    JMethod dispatchedMethod = dispatch(now, m.getSubsignature());
                    if(dispatchedMethod != null){
                        targets.add(dispatchedMethod);
                    }
                    if(now.isInterface()){
                        subTypes.addAll(hierarchy.getDirectSubinterfacesOf(now));
                        subTypes.addAll(hierarchy.getDirectImplementorsOf(now));
                    }else{
                        subTypes.addAll(hierarchy.getDirectSubclassesOf(now));
                    }
                }
            }
            case VIRTUAL -> {
                JClass C = m.getDeclaringClass();
                Queue<JClass> subTypes = new LinkedList<>();
                subTypes.add(C);
                // BFS 遍历类的所有子类
                while (!subTypes.isEmpty()) {
                    JClass now = subTypes.poll();
                    JMethod dispatchedMethod = dispatch(now, m.getSubsignature());
                    if (dispatchedMethod != null) {
                        targets.add(dispatchedMethod);
                    }
                    if (now.isInterface()) {
                        subTypes.addAll(hierarchy.getDirectSubinterfacesOf(now));
                        subTypes.addAll(hierarchy.getDirectImplementorsOf(now));
                    } else {
                        subTypes.addAll(hierarchy.getDirectSubclassesOf(now));
                    }
                }
            }
        }
        return targets;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if(jclass == null) {
            return null;
        }

        final JMethod[] res = new JMethod[1];
        jclass.getDeclaredMethods().forEach(method -> {
            if(method.getSubsignature().equals(subsignature)) {
                res[0] = method;
            }
        });
        // WAx2: Abstract Method
        if(res[0] != null && !res[0].isAbstract()) {
            return res[0];
        }else if(jclass.getSuperClass() != null) {
            return dispatch(jclass.getSuperClass(), subsignature);
        }else{
            return null;
        }
    }
}
