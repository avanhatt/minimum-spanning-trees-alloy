sig Vertex {
    neighbors : set Vertex -> Graph //all vertices that a given vertex is directly connected to
}
{
	Vertex in Graph.vertices
}

sig Edge {
	v1 : one Vertex,
	v2 : one Vertex,
	weight : Int,
	graphs : set Graph, //the graphs that the edge is part of
	rels : set Vertex -> Vertex // a relation connecting v1 and v2
}
{
	Edge in Graph.edges // all edges are in a graph
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
	all e: edges | 
		e.rels =  e.v1->e.v2 + e.v2->e.v1
}

sig DGraph extends Graph {}
{
	directedNeighbors
	all e: edges | 
		e.rels =  e.v1->e.v2
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
	// there are no two edges that connect the same pair of vertices (in either direction)
    	all disj edge1, edge2 : g.edges |  { 
            let verts1 = edge1.v1 + edge1.v2 |
           		 let verts2 = edge2.v1 + edge2.v2 |
            	 verts1 != verts2
    	}
}

pred twoWayNoDuplicateEdges {
	all g: Graph |
	// there are no two edges that connect the same two vertices (in the same direction)
    	all disj edge1, edge2 : g.edges |
        	edge1.v1 = edge2.v1 implies edge1.v2 != edge2.v2
}

pred undirectedNeighbors {
	//for each vertex, its neighbors are all vertices with whom it shares an edge
	all g: Graph |
		all x, y: Vertex |
			y in x.neighbors.g iff {
				some e: g.edges |
					(x = e.v1 and y = e.v2) or
					(y = e.v1 and x = e.v2)
			}
}

pred directedNeighbors {
	// directed neighbors are only the neighbors such that there is an edge from the vertex to the neighbor
	all g: Graph |
		all x, y: Vertex |
			y in x.neighbors.g iff {
				some e: g.edges |
					x = e.v1 and y = e.v2
			}
}
