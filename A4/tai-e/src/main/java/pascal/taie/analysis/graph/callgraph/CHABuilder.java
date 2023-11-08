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
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.lang.invoke.CallSite;
import java.util.*;

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
        callGraph.addReachableMethod(entry);
        var RM = new HashSet<JMethod>();
        Queue<JMethod> WL = new LinkedList<>();
        WL.add(entry);
        while(!WL.isEmpty()){
            var m = WL.poll();
            if (!RM.contains(m)){
                RM.add(m);
                for(var stmt: m.getIR()){
                    if (stmt instanceof Invoke cs){
                        var T = resolve(cs);
                        for(var m1: T){
                            if (!callGraph.contains(m1)){
                                callGraph.addReachableMethod(m1);
                            }
                            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs.getInvokeExp()), cs, m1));
                            WL.add(m1);
                        }
                    }
                }
            }
        }
        return callGraph;
    }


    private void dfsDispatch(JClass cur_class, Subsignature subsignature, Set<JMethod> T){
        if (!dispatch(cur_class, subsignature).isAbstract())  T.add(dispatch(cur_class, subsignature));
        for(var subclass: hierarchy.getDirectSubclassesOf(cur_class)){
            dfsDispatch(subclass, subsignature, T);
        }
    }
    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        var T = new HashSet<JMethod>();
        var cls = callSite.getMethodRef().getDeclaringClass();
        var subsig = callSite.getMethodRef().getSubsignature();
        if (callSite.isStatic()){
            T.add(dispatch(cls, subsig));
        }else if (callSite.isSpecial()){
            T.add(dispatch(cls, subsig));
        }else if (callSite.isVirtual()){
            dfsDispatch(cls, subsig, T);
        }else if (callSite.isInterface()){
            for (var implcls: hierarchy.getDirectImplementorsOf(cls)){
                dfsDispatch(implcls, subsig, T);
            }
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if (jclass == null) return null;
        if (jclass.getDeclaredMethod(subsignature) != null){
            return jclass.getDeclaredMethod(subsignature);
        }else{
            return dispatch(jclass.getSuperClass(), subsignature);
        }
    }
}
