sig Vertex {
    neighbors : set Vertex -> Graph
}
{
	Vertex in Graph.vertices
}

sig Edge {
	v1: one Vertex,
	v2: one Vertex,
	weight: Int,
	graphs: set Graph,
	rels: set Vertex -> Vertex
}
{
	Edge in Graph.edges
	rels =  v1->v2 + v2->v1
}

abstract sig Graph {
	edges: set Edge,
	vertices: set Vertex
}
{
	edgesInGraph
	noSelfEdges
	oneWayNoDuplicateEdges
}

sig UGraph extends Graph {}
{
	twoWayNoDuplicateEdges
	undirectedNeighbors
}

sig DGraph extends Graph {}
{
	directedNeighbors
}

pred edgesInGraph{
	all g: Graph |
    	all e: Edge |
        	e in g.edges iff {
            	g in e.graphs
            	e.v1 in g.vertices
            	e.v2 in g.vertices
        	}
}

pred noSelfEdges {
	all g: Graph |
    	no edge: g.edges |
        	edge.v1 = edge.v2
}

pred oneWayNoDuplicateEdges {
	all g: Graph |
    	all disj edge1, edge2 : g.edges |  { 
            let verts1 = edge1.v1 + edge1.v2 |
           		 let verts2 = edge2.v1 + edge2.v2 |
            	 verts1 != verts2
    	}
}

pred twoWayNoDuplicateEdges {
	all g: Graph |
    	all disj edge1, edge2 : g.edges |
        	edge1.v1 = edge2.v1 implies edge1.v2 != edge2.v2
}

pred undirectedNeighbors {
	all g: Graph |
		all x, y: Vertex |
			y in x.neighbors.g iff {
				some e: g.edges |
					(x = e.v1 and y = e.v2) or
					(y = e.v1 and x = e.v2)
			}
}

pred directedNeighbors {
	all g: Graph |
		all x, y: Vertex |
			y in x.neighbors.g iff {
				some e: g.edges |
					x = e.v1 and y = e.v2
			}
}

run {}
