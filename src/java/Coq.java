import java.util.*;
import java.io.*;

public class Coq {
    public static <T extends Object> void iterableToCoq (Iterable<T> list, PrintWriter writer) {
	writer.print("(");
	for (T i : list) {
	    writer.print(i + " :: ");
	}
	writer.print("nil)");
    }
}
