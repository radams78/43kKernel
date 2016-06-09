import java.util.*;

/* 
 * Contains the signature function value for all inputs to "allValidInputs()" of a region.
 * Two regions whose boundary are the same and have the same signature are "equivalent",
 * Two regions with different boundary could theoretically have the same signature (and not
 * be equivalent).
 */
public class Signature {

	ArrayList<Integer> sig;
	
	Signature(ArrayList<Integer> setSig) {sig = setSig;}
	public int get(int p) {return sig.get(p);}
	public int size() {return sig.size();}
	public ArrayList<Integer> getSignatureCopy() {return new ArrayList<Integer> (sig);}
	
	BitSet store() {
		BitSet ans = new BitSet ();
		int p = 0;
		for(int i = 0; i < sig.size(); ++i) {
			int v = get(i);
			if(v >= 1) ans.set(p);
			if(v >= 2) ans.set(p+1);
			p += 2;
		}
		return ans;
	}

	public String toString() {return sig.toString();}

	public boolean equals(Object o) {
		if(!(o instanceof Signature)) return false;
		return sig.equals( ((Signature) o).sig);
	}

}
