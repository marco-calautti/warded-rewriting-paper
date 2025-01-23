/*
 * Integrated Rule Inference System (IRIS+-):
 * An extensible rule inference system for datalog with extensions.
 * 
 * Copyright (C) 2009 ICT Institute - Dipartimento di Elettronica e Informazione (DEI), 
 * Politecnico di Milano, Via Ponzio 34/5, 20133 Milan, Italy.
 * 
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 * 
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, 
 * MA  02110-1301, USA.
 */
package org.deri.iris.queryrewriting;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.deri.iris.api.basics.IPosition;

/**
 * @author Giorgio Orsi <orsi@elet.polimi.it> - Politecnico di Milano
 * @version 1.0
 */
public class PredicateJoinTable {
    
    private Map<IPosition, Set<IPosition>> map;
    
    public PredicateJoinTable () {
	map = new HashMap<IPosition, Set<IPosition>>();
    }
    
    public boolean contains (IPosition p) {
	return (map.containsKey(p));
    }
    
    public void addPosition(IPosition p) {
	map.put(p, new HashSet<IPosition>());
    }
    
    public void addJoin(IPosition p1, IPosition p2) {
	map.get(p1).add(p2);
    }
    
    public int getJoinCount() {
	int count = 0;
	for (IPosition p : map.keySet())
	    count += map.get(p).size();
	return (count/2);
    }
    
    public String toString() {
	String out = "";
	if (map.size()>0)
	    for (IPosition lp : map.keySet()) {
		Set<IPosition> sp = map.get(lp);
		out += "///" + lp + ">< {";
		for (IPosition rp : sp) 
		    out += rp + ", ";
		out = out.substring(0, out.length()-2);
		out += "} [" + sp.size() + "]///\n"; 
	    }
	else 
	    out += "///[]///";
	return (out);
    }
    
    public int size() {
	return (map.size());
    }
    
    public IPosition getTopJoin() {
	// Sort w.r.t. the size of the right predicates
	Iterator<IPosition> it = map.keySet().iterator();
	IPosition max = it.next();
	while (it.hasNext()) {
	    IPosition cur = it.next();
	    if (map.get(cur).size() > map.get(max).size())
		max = cur;
	}
	return (max);
    }

    public void removePosition(IPosition p) {
	map.remove(p);
    }
    
    public Set<IPosition> getJoins(IPosition p) {
	return (map.get(p));
    }
}
