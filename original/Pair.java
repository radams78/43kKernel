
// Comparable Pair, compares first on first, then on second.
public class Pair<F, S> {
	public F first;
	public S second;
	
	Pair() {
		first = null;
		second = null;
	}
	
	public Pair(F first, S second) {
		this.first = first;
		this.second = second;
	}
	
	// copy constructor
	public Pair(Pair<F,S> P) {this(P.first, P.second);}
	
	public String toString() {
		return "[" + first.toString() + "," + second.toString() + "]";	
	}	

	public boolean equals(Object o) {
		if (!(o instanceof Pair)) return false;
		Pair<?, ?> pair = (Pair<?, ?>) o;
		return first.equals(pair.first) && second.equals(pair.second);
	}	
	
	public static void main(String[] args) {
		Pair<String, String> P = new Pair<String, String> ("abra", "kadabra");	
		Pair<String, String> P2 = new Pair<String, String> ("abro", "badabra");
		System.out.println(P);
		System.out.println(P2); 		
 	}	
    
	public int hashCode() {
        return (first == null ? 0 : first.hashCode()) ^ (second == null ? 0 : second.hashCode());
    }
	
}