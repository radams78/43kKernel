import java.util.*;

/* @inv Every object in list should have Coq type type */
public class CoqList<T extends CoqObject> extends ArrayList<T> implements CoqObject {
    private String name;
    private String type;

    public CoqList (List<T> list, String name) {
	testInvariants();
    }

    public CoqList(String name) {
	testInvariants();
    }

    public CoqList(CoqList<T> coqList) {
	testInvariants();
    }
    
    public void testInvariants() {
	for (T x : this) {
	    assert x.getType().equals(type);
	}
    }

    public String getName() {
	return name;
    }

    public String getType() {
	return "list " + type;
    }

    public String toCoq() {
	String result = "";
	for (T x : this) {
	    result += x.toCoq();
	}
	result += "Definition " + name + " : list " + type + " :=\n";
	for (T x : this) {
	    result += "  " + x.getName() + " :: \n";
	}
	result += "  :: nil.\n\n";
	return result;
    }
}
