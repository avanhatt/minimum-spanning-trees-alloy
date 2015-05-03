open util/integer
open util/ordering[State]
open lib/graph
open MST
open lib/properties

sig State {
	// The graph we're operating on
	g : one UGraph,

	// Clouds
	parentSet : Vertex -> Vertex,

	// Edges we haven't tried to add yet
	remainingEdges : set Edge,

	// The edges that we've already added to our MST
	edgesInMST : set Edge
}{
	some g.edges
}

fun minEdge(es : set Edge) : Edge {
	// This non-deterministically returns one of the edges of the smallest weight if there are multiple
	{e : es | no e2 : es | lt[e2.weight, e.weight]}
}

pred isAddable(e : Edge, s : State) {
	// If they're in different trees, this edge is addable
	no e.v1.^(s.parentSet) & e.v2.^(s.parentSet)
}

fact initialState {
	// Otherwise this will return a spanning forest instead of a spanning tree
	connected[first.g.edges, first.g.vertices]

	// All parent pointers start off pointing to themselves
	all v1, v2 : Vertex |
		v1->v2 in first.parentSet iff (v1 = v2) and (v1 in first.g.vertices)

	first.remainingEdges = first.g.edges
	no first.edgesInMST
}

fact endState {
	no last.remainingEdges
	isMST[last.edgesInMST, last.g]
}

abstract sig Event {
	pre, post : State
}

sig addEdge extends Event { }
{
	// These all must be operating on the same graph!
	post.g = pre.g

	// Go in order of edge weight
	let minE = minEdge[pre.remainingEdges] {
		isAddable[minE, pre] => {
			// Add it to the MST and update the parent pointers
			post.edgesInMST = pre.edgesInMST + minE
			post.parentSet = pre.parentSet - (minE.v1 -> minE.v1) + (minE.v1 -> minE.v2)
		} else {
			// The clouds/MST are still the same
			post.edgesInMST = pre.edgesInMST
			post.parentSet = pre.parentSet
		}
		post.remainingEdges = pre.remainingEdges - minE
	}
}

fact transitions {
	all s: State - last |
		let s' = s.next |
			one e: Event | e.pre = s and e.post = s'
}

run { } for 10 Int, exactly 6 Edge, 1 Graph, 4 Vertex, 7 State, 6 Event
