import java.util.*;

public class VertexRenamer {
    private TreeMap<Vertex, Vertex> nameList;
	
    VertexRenamer(ArrayList<Vertex> L) {
	nameList = new TreeMap<Vertex, Vertex> (); 
	for(int i = 0; i < L.size(); ++i) {
	    nameList.put(L.get(i), i);
	}
    }
	
    VertexRenamer(TreeMap<Vertex, Vertex> nameList) {
	this.nameList = nameList;
    }
	
    int nameOf(int v) {return nameList.get(v);}
	
    public VertexRenamer inverseMap() {
	TreeMap<Vertex, Vertex> ans = new TreeMap<Vertex, Vertex> ();
	
	for(int k : nameList.keySet()) {
	    ans.put(nameList.get(k), k);
	}
	
	return new VertexRenamer(ans); 	
    }
    
    // Returns a new Vertex Renamer where each value is increased by x.
    public VertexRenamer addX(int x) {
	TreeMap<Vertex, Vertex> M = new TreeMap<Vertex, Vertex> ();
	for(int k : nameList.keySet()) M.put(k, nameList.get(k) + x);
	return new VertexRenamer(M);
    } 
    
    
    public Boundary renamedBoundary(Boundary b) {
	ArrayList<Vertex> topPath = new ArrayList<Vertex> ();
	for(int i = 0; i < b.topPathLength() + 2; ++i) {topPath.add(nameOf(b.topPathVertex(i)));}
	
	ArrayList<Vertex> bottomPath = new ArrayList<Vertex> ();
	for(int i = 0; i < b.bottomPathLength() + 2; ++i) {bottomPath.add(nameOf(b.bottomPathVertex(i)));}
	
	return new Boundary(topPath, bottomPath);
    }
    
    public TreeSet<Vertex> renamedSet(Set<Vertex> S) {
	TreeSet<Vertex> ans = new TreeSet<Vertex> ();
	for(int s : S) ans.add(nameOf(s));
	return ans;
    }
    
    // makes a new VertexRenamer that first applies this and then r to the output.
    public VertexRenamer compose(VertexRenamer r) {
	TreeMap<Vertex, Vertex> ans = new TreeMap<Vertex, Vertex> ();
	for(int v : nameList.keySet()) ans.put(v, r.nameOf(nameOf(v)));
	return new VertexRenamer(ans);
    }
    
    public String toString() {return nameList.toString();}
    
}
