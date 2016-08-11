public class Vertex extends CoqObject implements Comparable<Vertex> {
    public final static String COQTYPE = CoqObject.NAT;

    private final int index;

    public Vertex(int n) {
	super(COQTYPE, Integer.toString(n));
	this.index = n;
    }

    public Vertex plus(int n) {
	return new Vertex(index + n);
    }

    public int compareTo(Vertex n) {
	return new Integer(index).compareTo(new Integer(n.index));
    }

    @Override public String toString() {
	return Integer.toString(index);
    }

    @Override public boolean equals(Object n) {
	if (n instanceof Vertex) {
	    Vertex nn = (Vertex) n;
	    return index == nn.index;
	}
	return false;
    }

    @Override public int hashCode() {
	return index;
    }
}
