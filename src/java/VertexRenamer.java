import java.util.*;

public class VertexRenamer {
    private TreeMap<Vertex, Vertex> nameList;
	
    VertexRenamer(ArrayList<Vertex> L) {
	nameList = new TreeMap<Vertex, Vertex> (); 
	for(int i = 0; i < L.size(); ++i) {
	    nameList.put(L.get(i), new Vertex(i));
	}
    }
	
    VertexRenamer(TreeMap<Vertex, Vertex> nameList) {
	this.nameList = nameList;
    }
	
    Vertex nameOf(Vertex v) {return nameList.get(v);}
	
    public VertexRenamer inverseMap() {
	TreeMap<Vertex, Vertex> ans = new TreeMap<Vertex, Vertex> ();
	
	for(Vertex k : nameList.keySet()) {
	    ans.put(nameList.get(k), k);
	}
	
	return new VertexRenamer(ans); 	
    }
    
    // Returns a new Vertex Renamer where each value is increased by x.
    public VertexRenamer addX(int x) {
	TreeMap<Vertex, Vertex> M = new TreeMap<Vertex, Vertex> ();
	for(Vertex k : nameList.keySet()) M.put(k, nameList.get(k).plus(x));
	return new VertexRenamer(M);
    } 
    
    
    public Boundary renamedBoundary(Boundary b) {
	Vertex[] topPath = new Vertex[b.topPathLength().toInt + 2];
	for(int i = 0; i < b.topPathLength().toInt + 2; ++i) topPath[i] = nameOf(b.topPathVertex(i)); // TODO Magic constant
	
	Vertex[] bottomPath = new Vertex[b.bottomPathLength().toInt + 2];
	for(int i = 0; i < b.bottomPathLength().toInt + 2; ++i) bottomPath[i] = nameOf(b.bottomPathVertex(i)); // TODO Duplication
	
	return new Boundary(new Path(Arrays.asList(topPath)), new Path(Arrays.asList(bottomPath))); // TODO Duplication
    }
    
    public TreeSet<Vertex> renamedSet(Set<Vertex> S) {
	TreeSet<Vertex> ans = new TreeSet<Vertex> ();
	for (Vertex s : S) ans.add(nameOf(s));
	return ans;
    }
    
    // makes a new VertexRenamer that first applies this and then r to the output.
    public VertexRenamer compose(VertexRenamer r) {
	TreeMap<Vertex, Vertex> ans = new TreeMap<Vertex, Vertex> ();
	for(Vertex v : nameList.keySet()) ans.put(v, r.nameOf(nameOf(v)));
	return new VertexRenamer(ans);
    }
    
    public String toString() {return nameList.toString();}
    
}
