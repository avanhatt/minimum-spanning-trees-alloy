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
}

abstract sig Event {
	pre, post : State
}

sig addEdge extends Event { }
{
	// These all must be operating on the same graph!
	post.g = pre.g

	// Go in order of edge weight
	let minEs = minEdge[pre.remainingEdges] {
		some minE : minEs | {
			isAddable[minE, pre] => {
				// Add it to the MST and update the parent pointers
				post.edgesInMST = pre.edgesInMST + minE
				let p1 = findParent[minE.v1, pre] |
					let p2 = findParent[minE.v2, pre] |
						post.parentSet = pre.parentSet - (p1->p1) + (p1->p2)
			} else {
				// The clouds/MST are still the same
				post.edgesInMST = pre.edgesInMST
				post.parentSet = pre.parentSet
			}
			post.remainingEdges = pre.remainingEdges - minE
		}
	}
}

fun findParent(v: Vertex, s: State) : Vertex {
	// parent is the root of the transitive closure (the one that is only related to itself)
	{parent: v.^(s.parentSet) | parent->parent in s.parentSet}
}

fact transitions {
	all s: State - last |
		let s' = s.next |
			one e: Event | e.pre = s and e.post = s'
}

assert findsMST {
	isMST[last.edgesInMST, last.g]
}

check findsMST for 10 Int, exactly 6 Edge, 1 Graph, 4 Vertex, 7 State, 6 Event

run { } for 10 Int, exactly 6 Edge, 1 Graph, 4 Vertex, 7 State, 6 Event
