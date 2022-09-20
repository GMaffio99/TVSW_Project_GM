package mortal_chess_tests;

import static org.junit.Assert.*;

import java.io.BufferedReader;
import java.io.IOException;

import org.junit.Test;
import static org.mockito.Mockito.*;

import mortal_chess.Partita;
import mortal_chess.Tavolo;

public class PartitaTest {

	@Test
	public void testSelezioneCella() throws IOException {
		// setup mocked input reader
		BufferedReader mockReader = mock(BufferedReader.class);
		when(mockReader.readLine()).thenReturn("") // no stringa vuota
								   .thenReturn("A") // no stringa di 1 carattere
								   .thenReturn("A0") // no riga 0
								   .thenReturn("I1") // no colonna I
								   .thenReturn("A10") // no stringa di 3 caratteri
								   .thenReturn("A1"); // ok
		// setup tavolo
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		// test
		Partita partita = new Partita(mockReader, tavolo);
		assertEquals(partita.selezioneCella("SELEZIONA CELLA"), "A1");
	}

	@Test
	public void testIsInteger() {
		Partita partita = new Partita(null, null);
		assertTrue(partita.isInteger("1"));
		assertTrue(partita.isInteger("100"));
		assertTrue(partita.isInteger("-3"));
		assertFalse(partita.isInteger("")); // no stringa vuota
		assertFalse(partita.isInteger("0.1")); // no numero decimale
		assertFalse(partita.isInteger("0,1")); // no numero decimale
		assertFalse(partita.isInteger("ABC")); // no stringa testuale
	}

	@Test
	public void testImpostaPunti() throws IOException {
		// setup mocked input reader
		BufferedReader mockReader = mock(BufferedReader.class);
		when(mockReader.readLine()).thenReturn("dieci") // no numero testuale
								   .thenReturn("-10") // no numero negativo
								   .thenReturn("0") // no numero nullo
								   .thenReturn("5"); // ok
		// setup tavolo
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		// test
		Partita partita = new Partita(mockReader, tavolo);
		partita.impostaPunti();
		assertEquals(tavolo.getPuntiGiocatoreX(), 5);
		assertEquals(tavolo.getPuntiGiocatoreO(), 5);
	}

	@Test
	public void testSelezionaMossa() throws IOException {
		// setup mocked input reader
		BufferedReader mockReader = mock(BufferedReader.class);
		when(mockReader.readLine()).thenReturn("0") // no mossa < 1
								   .thenReturn("6") // no mossa > 5
								   .thenReturn("11") // no mossa > 5
								   .thenReturn("") // no stringa vuota
								   .thenReturn(" ") // no stringa spazio
								   .thenReturn("A") // no lettera
								   .thenReturn("1"); // ok
//								   .thenReturn("2") // ok
//								   .thenReturn("3") // ok
//								   .thenReturn("4") // ok
//								   .thenReturn("5"); // ok
		// setup tavolo
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		// test
		Partita partita = new Partita(mockReader, tavolo);
		assertEquals(partita.selezionaMossa('X', "SELEZIONA MOSSA"), '1');
//		assertEquals(partita.selezionaMossa('X', "SELEZIONA MOSSA"), '2');
//		assertEquals(partita.selezionaMossa('X', "SELEZIONA MOSSA"), '3');
//		assertEquals(partita.selezionaMossa('X', "SELEZIONA MOSSA"), '4');
//		assertEquals(partita.selezionaMossa('X', "SELEZIONA MOSSA"), '5');
	}

	@Test
	public void testPosizionarePedina() throws IOException {
		// setup mocked input reader
		BufferedReader mockReader = mock(BufferedReader.class);
		when(mockReader.readLine()).thenReturn("Attaccante") // no stringa "Attaccante"
								   .thenReturn("Difensore") // no stringa "Difensore"
								   .thenReturn("AD") // no AttaccanteDifensore
								   .thenReturn("A") // ok
								   .thenReturn("B1") // no colonna 'B' per giocatore X
								   .thenReturn("A1") // cella occupata
								   .thenReturn("A2"); // ok
		// setup tavolo
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		tavolo.posizionaPedina('X', 'D', '1', 'A');
		// test
		Partita partita = new Partita(mockReader, tavolo);
		assertNull(tavolo.getPedina('2', 'A'));
		partita.posizionarePedina('X', "[X]");
		assertNotNull(tavolo.getPedina('2', 'A'));
	}

	@Test
	public void testMuoverePedina() throws IOException {
		// setup mocked input reader
		BufferedReader mockReader = mock(BufferedReader.class);
		when(mockReader.readLine()).thenReturn("H1") // pedina appartenente all'avversario
								   .thenReturn("A1") // pedina non può essere mossa
								   .thenReturn("A6") // cella vuota
								   .thenReturn("A7") // ok
								   .thenReturn("C7") // cella non raggiungibile
								   .thenReturn("A8") // cella occupata
								   .thenReturn("B7"); // ok
		// setup tavolo
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		tavolo.posizionaPedina('O', 'A', '1', 'H');
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('X', 'A', '2', 'A');
		tavolo.posizionaPedina('X', 'A', '1', 'B');
		tavolo.posizionaPedina('X', 'A', '2', 'B');
		tavolo.posizionaPedina('X', 'A', '7', 'A');
		tavolo.posizionaPedina('X', 'A', '8', 'A');
		// test
		Partita partita = new Partita(mockReader, tavolo);
		assertNotNull(tavolo.getPedina('7', 'A'));
		assertNull(tavolo.getPedina('7', 'B'));
		partita.muoverePedina('X', "[X]");
		assertNull(tavolo.getPedina('7', 'A'));
		assertNotNull(tavolo.getPedina('7', 'B'));
	}

	@Test
	public void testUnirePedine() throws IOException {
		// setup mocked input reader
		BufferedReader mockReader = mock(BufferedReader.class);
		when(mockReader.readLine()).thenReturn("H1") // pedina appartenente all'avversario
								   .thenReturn("A1") // pedina non può essere unita
								   .thenReturn("A2") // cella vuota
								   .thenReturn("A7") // ok
								   .thenReturn("B7") // pedina appartenente all'avversario
								   .thenReturn("A5") // pedine non adiacenti
								   .thenReturn("A6") // cella vuota
								   .thenReturn("A8"); // ok
		// setup tavolo
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		tavolo.posizionaPedina('O', 'A', '1', 'H');
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('X', 'A', '7', 'A');
		tavolo.posizionaPedina('O', 'A', '7', 'B');
		tavolo.posizionaPedina('X', 'A', '5', 'A');
		tavolo.posizionaPedina('X', 'A', '8', 'A');
		// test
		Partita partita = new Partita(mockReader, tavolo);
		assertNotNull(tavolo.getPedina('7', 'A'));
		assertNotNull(tavolo.getPedina('8', 'A'));
		partita.unirePedine('X', "[X]");
		assertNotNull(tavolo.getPedina('7', 'A'));
		assertNull(tavolo.getPedina('8', 'A'));
	}

	@Test
	public void testAttaccarePedina() throws IOException {
		// setup mocked input reader
		BufferedReader mockReader = mock(BufferedReader.class);
		when(mockReader.readLine()).thenReturn("H1") // pedina appartenente all'avversario
								   .thenReturn("A1") // pedina non ha avversari adiacenti
								   .thenReturn("A2") // cella vuota
								   .thenReturn("A3") // pedina non attaccante
								   .thenReturn("A7") // ok
								   .thenReturn("A8") // pedina non appartenente all'avversario
								   .thenReturn("C7") // pedine non attaccabile
								   .thenReturn("A6") // cella vuota
								   .thenReturn("B7"); // ok
		// setup tavolo
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		tavolo.posizionaPedina('O', 'A', '1', 'H');
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('X', 'D', '3', 'A');
		tavolo.posizionaPedina('X', 'A', '7', 'A');
		tavolo.posizionaPedina('O', 'A', '7', 'B');
		tavolo.posizionaPedina('X', 'A', '8', 'A');
		tavolo.posizionaPedina('O', 'A', '7', 'C');
		// test
		Partita partita = new Partita(mockReader, tavolo);
		assertNotNull(tavolo.getPedina('7', 'A'));
		assertNotNull(tavolo.getPedina('7', 'B'));
		partita.attaccarePedina('X', "[X]");
		assertNull(tavolo.getPedina('7', 'A'));
		assertNull(tavolo.getPedina('7', 'B'));
	}

	@Test
	public void testAttaccareAvversario() throws IOException {
		// setup mocked input reader
		BufferedReader mockReader = mock(BufferedReader.class);
		when(mockReader.readLine()).thenReturn("H1") // pedina appartenente all'avversario
								   .thenReturn("A1") // pedina non può attaccare l'avversario
								   .thenReturn("H2") // cella vuota
								   .thenReturn("H3") // pedina non attaccante
								   .thenReturn("H4"); // ok
		// setup tavolo
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		tavolo.posizionaPedina('O', 'A', '1', 'H');
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('X', 'D', '3', 'H');
		tavolo.posizionaPedina('X', 'A', '4', 'H');
		// test
		Partita partita = new Partita(mockReader, tavolo);
		assertNotNull(tavolo.getPedina('4', 'H'));
		assertEquals(tavolo.getPuntiGiocatoreO(), 10);
		partita.attaccareAvversario('X', "[X]");
		assertNull(tavolo.getPedina('4', 'H'));
		assertEquals(tavolo.getPuntiGiocatoreO(), 9);
	}

}
