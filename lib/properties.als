open util/integer
open graph

//determines if a set of edges and vertices would form a directed acyclic graph
pred directedAcyclic (edges : set Edge, verts : set Vertex) {
	--verts = Vertex.(edges.rels)
	all e : edges |
		e.v1 + e.v2 in verts
	all v1, v2: verts |
		//for any edge in the graph, if the edge is removed, v2 is not reachable from v1
		let e = v1->v2 |
			e in edges.rels implies
				e not in ^(edges.rels - e)
}

//determines if a set of edges and vertices would form a complete graph
pred complete (edges : set Edge, verts : set Vertex) {
	all e : edges |
		e.v1 + e.v2 in verts
	//for each pair of vertices, there is an edge connecting them
	all disj x, y : verts |
		some e : edges |
			(e.v1 = x and e.v2 = y) or (e.v2 = x and e.v1 = y)
}

//determines if a set of edges and vertices would form an undirected acyclic graph
pred undirectedAcyclic (edges : set Edge, verts : set Vertex) {
	all e : edges |
		e.v1 + e.v2 in verts
	all v1, v2: verts |
		let e = v1->v2 + v2->v1|
			//for any edge in the graph (pair in both directions because it's undirected), if the edge is removed,
			//v1 and v2 are no longer reachable from each other
			e in edges.rels implies
				e not in ^(edges.rels - e)
}

//determines if a set of edges and vertices would form a connected graph
pred connected (edges: set Edge, verts: set Vertex) {
	all e : edges |
		e.v1 + e.v2 in verts
	//all vertices are reachable from all other vertices
	all disj v1, v2 : verts |
		v1 in v2.^(edges.rels)
}

run connected
