import java.util.*;
import java.io.*;

public class VertexTest {
    public static final Vertex a = new Vertex(0);
    public static final Vertex b = new Vertex(1);
    public static final Vertex c = new Vertex(2);

    /* Test we have implemented equals correctly */
    public static void main(String[] args) {
	Vertex a = new Vertex(0);
	Vertex b = new Vertex(0);
	ArrayList<Vertex> aa = new ArrayList<Vertex>();
	aa.add(b);
	assert aa.contains(a);
    }
}
