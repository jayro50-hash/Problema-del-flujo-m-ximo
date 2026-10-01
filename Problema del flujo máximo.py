
import tkinter as tk
from tkinter import ttk
from tkinter import messagebox
from tkinter import scrolledtext
import random
from collections import deque

import networkx as nx
import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg


NODOS_MINIMOS = 7
NODOS_MAXIMOS = 16
CAPACIDAD_MINIMA = 1
CAPACIDAD_MAXIMA = 20
PROBABILIDAD_ARISTA_EXTRA = 0.3


NOMBRE_UNIVERSIDAD_LINEA_1 = "UPC"
NOMBRE_UNIVERSIDAD_LINEA_2 = "Universidad Peruana de Ciencias Aplicadas"
NOMBRES_INTEGRANTES = [
    "Jayro Sebastian Gabira Zuñiga",
    "Diego Edson Alvarez Leandro",
    "Elehazar Nicolas Muñoz Perales",
    "Mathias Tiziano Huiza Vilca",
]

COLOR_FONDO_OSCURO = "#16233c"
COLOR_ACENTO = "#f4a300"
COLOR_TEXTO_CLARO = "#ffffff"
COLOR_TEXTO_SECUNDARIO = "#9fb0c3"
COLOR_FONDO_CLARO = "#f0f0f0"

class GrafoFlujo:

    def __init__(self, cantidad_nodos):
        self.cantidad_nodos = cantidad_nodos
        self.nombres_nodos = []
        indice = 0
        while indice < cantidad_nodos:
            self.nombres_nodos.append("N" + str(indice))
            indice = indice + 1

        self.capacidades = {}
        self.flujos = {}

    def agregar_nodo_ficticio(self, nombre):
        if nombre not in self.nombres_nodos:
            self.nombres_nodos.append(nombre)

    def existe_arista(self, origen, destino):
        clave = (origen, destino)
        if clave in self.capacidades:
            return True
        else:
            return False

    def agregar_arista(self, origen, destino, capacidad):
        clave = (origen, destino)
        self.capacidades[clave] = capacidad
        self.flujos[clave] = 0

    def eliminar_arista(self, origen, destino):
        clave = (origen, destino)
        if clave in self.capacidades:
            del self.capacidades[clave]
        if clave in self.flujos:
            del self.flujos[clave]

    def obtener_vecinos_salientes(self, nodo):
        vecinos = []
        for clave in self.capacidades.keys():
            origen = clave[0]
            destino = clave[1]
            if origen == nodo:
                vecinos.append(destino)
        return vecinos

    def tiene_ciclo(self):
        estado = {}
        for nodo in self.nombres_nodos:
            estado[nodo] = 0 

        for nodo in self.nombres_nodos:
            if estado[nodo] == 0:
                hay_ciclo = self._dfs_deteccion_ciclo(nodo, estado)
                if hay_ciclo:
                    return True
        return False

    def _dfs_deteccion_ciclo(self, nodo_actual, estado):
        estado[nodo_actual] = 1
        vecinos = self.obtener_vecinos_salientes(nodo_actual)

        for vecino in vecinos:
            if estado[vecino] == 1:
                return True
            elif estado[vecino] == 0:
                hay_ciclo = self._dfs_deteccion_ciclo(vecino, estado)
                if hay_ciclo:
                    return True

        estado[nodo_actual] = 2
        return False

    def obtener_capacidad_residual(self, origen, destino):
        clave_directa = (origen, destino)
        clave_inversa = (destino, origen)

        if clave_directa in self.capacidades:
            capacidad_original = self.capacidades[clave_directa]
            flujo_actual = self.flujos[clave_directa]
            return capacidad_original - flujo_actual
        elif clave_inversa in self.capacidades:
            flujo_actual = self.flujos[clave_inversa]
            return flujo_actual
        else:
            return 0

    def obtener_vecinos_residuales(self, nodo):
        vecinos = set()
        for clave in self.capacidades.keys():
            origen = clave[0]
            destino = clave[1]
            if origen == nodo:
                vecinos.add(destino)
            if destino == nodo:
                vecinos.add(origen)
        return vecinos

    def actualizar_flujo_en_camino(self, camino, cantidad):
        indice = 0
        while indice < len(camino) - 1:
            origen = camino[indice]
            destino = camino[indice + 1]
            clave_directa = (origen, destino)
            clave_inversa = (destino, origen)

            if clave_directa in self.capacidades:
                self.flujos[clave_directa] = self.flujos[clave_directa] + cantidad
            elif clave_inversa in self.capacidades:
                self.flujos[clave_inversa] = self.flujos[clave_inversa] - cantidad

            indice = indice + 1

class FordFulkerson:

    def __init__(self, grafo, fuente, sumidero):
        self.grafo = grafo
        self.fuente = fuente
        self.sumidero = sumidero
        self.flujo_total = 0
        self.historial_caminos = []
        self.terminado = False

    def buscar_camino_aumento(self):
        padres = {}
        visitados = set()
        visitados.add(self.fuente)

        cola = deque()
        cola.append(self.fuente)

        while len(cola) > 0:
            nodo_actual = cola.popleft()

            if nodo_actual == self.sumidero:
                break

            vecinos = self.grafo.obtener_vecinos_residuales(nodo_actual)
            for vecino in vecinos:
                if vecino not in visitados:
                    capacidad_residual = self.grafo.obtener_capacidad_residual(nodo_actual, vecino)
                    if capacidad_residual > 0:
                        visitados.add(vecino)
                        padres[vecino] = nodo_actual
                        cola.append(vecino)

        if self.sumidero not in visitados:
            return None

        camino = [self.sumidero]
        nodo_actual = self.sumidero
        while nodo_actual != self.fuente:
            nodo_actual = padres[nodo_actual]
            camino.append(nodo_actual)
        camino.reverse()
        return camino

    def calcular_capacidad_minima(self, camino):
        capacidad_minima = None
        indice = 0
        while indice < len(camino) - 1:
            origen = camino[indice]
            destino = camino[indice + 1]
            capacidad_residual = self.grafo.obtener_capacidad_residual(origen, destino)
            if capacidad_minima is None:
                capacidad_minima = capacidad_residual
            elif capacidad_residual < capacidad_minima:
                capacidad_minima = capacidad_residual
            indice = indice + 1
        return capacidad_minima

    def ejecutar_un_paso(self):
        if self.terminado:
            return None

        camino = self.buscar_camino_aumento()
        if camino is None:
            self.terminado = True
            return None

        capacidad_minima = self.calcular_capacidad_minima(camino)
        self.grafo.actualizar_flujo_en_camino(camino, capacidad_minima)
        self.flujo_total = self.flujo_total + capacidad_minima

        informacion_paso = {}
        informacion_paso["camino"] = camino
        informacion_paso["capacidad"] = capacidad_minima
        informacion_paso["flujo_acumulado"] = self.flujo_total
        self.historial_caminos.append(informacion_paso)

        return informacion_paso

    def calcular_corte_minimo(self):
        visitados = set()
        visitados.add(self.fuente)

        cola = deque()
        cola.append(self.fuente)

        while len(cola) > 0:
            nodo_actual = cola.popleft()
            vecinos = self.grafo.obtener_vecinos_residuales(nodo_actual)
            for vecino in vecinos:
                if vecino not in visitados:
                    capacidad_residual = self.grafo.obtener_capacidad_residual(nodo_actual, vecino)
                    if capacidad_residual > 0:
                        visitados.add(vecino)
                        cola.append(vecino)

        aristas_corte = []
        for clave in self.grafo.capacidades.keys():
            origen = clave[0]
            destino = clave[1]
            if origen in visitados and destino not in visitados:
                aristas_corte.append(clave)

        return aristas_corte, visitados

class AplicacionFlujoMaximo(tk.Tk):

    def __init__(self):
        super().__init__()
        self.title("Problema del Flujo Maximo - Algoritmo de Ford-Fulkerson")
        self.geometry("1150x760")

        self.cantidad_nodos = 0
        self.grafo = None
        self.modo_construccion = tk.StringVar(value="manual")
        self.solucionador = None
        self.fuentes_seleccionadas = []
        self.sumideros_seleccionados = []
        self.nodo_fuente_final = None
        self.nodo_sumidero_final = None
        self.posiciones_layout = None
        self.respaldo_capacidades = None
        self.respaldo_flujos = None
        self.respaldo_nombres_nodos = None

        self.contenedor = tk.Frame(self)
        self.contenedor.pack(fill="both", expand=True)

        self.mostrar_pantalla_bienvenida()
        
    def limpiar_contenedor(self):
        lista_hijos = self.contenedor.winfo_children()
        for hijo in lista_hijos:
            hijo.destroy()

    def crear_boton_atras(self, marco_padre, comando):
        boton_atras = tk.Button(
            marco_padre, text="\u2190 Atras", command=comando,
            font=("Arial", 9, "bold"), relief="flat",
            bg="#e0e0e0", fg="#333333", padx=10, pady=4, cursor="hand2"
        )
        boton_atras.place(x=15, y=15)
        return boton_atras

    def mostrar_pantalla_bienvenida(self):
        self.limpiar_contenedor()
        self.contenedor.configure(bg=COLOR_FONDO_OSCURO)

        etiqueta_superior = tk.Label(
            self.contenedor, text="SIMULADOR DE", font=("Arial", 13, "bold"),
            bg=COLOR_FONDO_OSCURO, fg=COLOR_TEXTO_SECUNDARIO
        )
        etiqueta_superior.pack(pady=(50, 0))

        etiqueta_titulo = tk.Label(
            self.contenedor, text="FORD-FULKERSON", font=("Arial", 34, "bold"),
            bg=COLOR_FONDO_OSCURO, fg=COLOR_ACENTO
        )
        etiqueta_titulo.pack(pady=(0, 8))

        etiqueta_subtitulo = tk.Label(
            self.contenedor, text="Algoritmo de Flujo Maximo en Grafos Dirigidos",
            font=("Arial", 12), bg=COLOR_FONDO_OSCURO, fg=COLOR_TEXTO_CLARO
        )
        etiqueta_subtitulo.pack(pady=(0, 25))

        marco_descripcion = tk.Frame(
            self.contenedor, bg=COLOR_FONDO_OSCURO,
            highlightbackground=COLOR_ACENTO, highlightthickness=2
        )
        marco_descripcion.pack(padx=140, fill="x")

        texto_descripcion = (
            "Ford-Fulkerson calcula cuanto se puede enviar, como maximo, desde un punto A "
            "hasta un punto B a traves de una red con capacidades limitadas como tuberias "
            "o carreteras. Encuentra rutas libres una por una y envia por cada una lo que "
            "el tramo mas angosto le permita, hasta que ya no queda ninguna ruta disponible. "
            "Ahi esta el flujo maximo."
        )
        etiqueta_descripcion = tk.Label(
            marco_descripcion, text=texto_descripcion, font=("Arial", 11),
            bg=COLOR_FONDO_OSCURO, fg=COLOR_TEXTO_CLARO, justify="left",
            padx=20, pady=18, wraplength=780
        )
        etiqueta_descripcion.pack()

        boton_comenzar = tk.Button(
            self.contenedor, text="\u25B6  Comenzar Simulacion", font=("Arial", 12, "bold"),
            bg=COLOR_ACENTO, fg=COLOR_FONDO_OSCURO, activebackground="#ffb733",
            relief="flat", padx=18, pady=9, cursor="hand2",
            command=self.mostrar_pantalla_configuracion
        )
        boton_comenzar.pack(pady=28)

        marco_integrantes = tk.Frame(
            self.contenedor, bg=COLOR_FONDO_OSCURO,
            highlightbackground=COLOR_ACENTO, highlightthickness=2
        )
        marco_integrantes.pack(pady=5)

        etiqueta_titulo_integrantes = tk.Label(
            marco_integrantes, text="INTEGRANTES DEL GRUPO 4:", font=("Arial", 11, "bold"),
            bg=COLOR_FONDO_OSCURO, fg=COLOR_TEXTO_CLARO
        )
        etiqueta_titulo_integrantes.pack(pady=(16, 10), padx=50)

        for nombre_integrante in NOMBRES_INTEGRANTES:
            etiqueta_nombre = tk.Label(
                marco_integrantes, text="\u2022 " + nombre_integrante, font=("Arial", 10),
                bg=COLOR_FONDO_OSCURO, fg=COLOR_TEXTO_SECUNDARIO
            )
            etiqueta_nombre.pack(pady=3, padx=50)

        espaciador_final = tk.Label(marco_integrantes, text="", bg=COLOR_FONDO_OSCURO)
        espaciador_final.pack(pady=6)

        marco_pie = tk.Frame(self.contenedor, bg=COLOR_FONDO_OSCURO)
        marco_pie.pack(side="bottom", anchor="w", padx=25, pady=20)

        etiqueta_universidad_1 = tk.Label(
            marco_pie, text=NOMBRE_UNIVERSIDAD_LINEA_1, font=("Arial", 13, "bold"),
            bg=COLOR_FONDO_OSCURO, fg="#e2453c"
        )
        etiqueta_universidad_1.pack(anchor="w")

        etiqueta_universidad_2 = tk.Label(
            marco_pie, text=NOMBRE_UNIVERSIDAD_LINEA_2, font=("Arial", 9),
            bg=COLOR_FONDO_OSCURO, fg=COLOR_TEXTO_SECUNDARIO
        )
        etiqueta_universidad_2.pack(anchor="w")

    def mostrar_pantalla_configuracion(self):
        self.limpiar_contenedor()
        self.contenedor.configure(bg=COLOR_FONDO_CLARO)

        self.crear_boton_atras(self.contenedor, self.mostrar_pantalla_bienvenida)

        titulo = tk.Label(self.contenedor, text="Configuracion del Grafo", font=("Arial", 16, "bold"))
        titulo.pack(pady=15)

        marco_nodos = tk.Frame(self.contenedor)
        marco_nodos.pack(pady=10)

        etiqueta_nodos = tk.Label(marco_nodos, text="Cantidad de nodos (entre 7 y 16):")
        etiqueta_nodos.pack(side="left", padx=5)

        self.entrada_nodos = tk.Entry(marco_nodos, width=6)
        self.entrada_nodos.pack(side="left", padx=5)
        if self.cantidad_nodos > 0:
            self.entrada_nodos.insert(0, str(self.cantidad_nodos))

        marco_modo = tk.Frame(self.contenedor)
        marco_modo.pack(pady=10)

        etiqueta_modo = tk.Label(marco_modo, text="Modo de construccion del grafo:")
        etiqueta_modo.pack(anchor="w")

        opcion_manual = tk.Radiobutton(marco_modo, text="Manual", variable=self.modo_construccion, value="manual")
        opcion_manual.pack(anchor="w")

        opcion_aleatorio = tk.Radiobutton(marco_modo, text="Aleatorio", variable=self.modo_construccion, value="aleatorio")
        opcion_aleatorio.pack(anchor="w")

        boton_continuar = tk.Button(self.contenedor, text="Continuar", command=self.procesar_configuracion_inicial, font=("Arial", 11, "bold"))
        boton_continuar.pack(pady=20)

    def procesar_configuracion_inicial(self):
        texto_nodos = self.entrada_nodos.get().strip()

        if texto_nodos.isdigit() == False:
            messagebox.showerror("Error", "Debe ingresar un numero entero valido.")
            return

        cantidad = int(texto_nodos)
        if cantidad < NODOS_MINIMOS or cantidad > NODOS_MAXIMOS:
            messagebox.showerror("Error", "La cantidad de nodos debe estar entre 7 y 16.")
            return

        self.cantidad_nodos = cantidad
        self.grafo = GrafoFlujo(cantidad)

        modo = self.modo_construccion.get()
        if modo == "manual":
            self.mostrar_pantalla_manual()
        else:
            self.generar_grafo_aleatorio()
            self.mostrar_pantalla_seleccion()

    def determinar_cantidad_de_niveles(self):
        minimo_niveles = 4
        maximo_niveles = 6
        if maximo_niveles > self.cantidad_nodos - 1:
            maximo_niveles = self.cantidad_nodos - 1
        if minimo_niveles > maximo_niveles:
            minimo_niveles = maximo_niveles
        return random.randint(minimo_niveles, maximo_niveles)

    def repartir_nodos_en_niveles(self, cantidad_niveles):
        tamanos_de_niveles = []
        indice = 0
        while indice < cantidad_niveles:
            tamanos_de_niveles.append(1)
            indice = indice + 1

        nodos_restantes = self.cantidad_nodos - cantidad_niveles
        while nodos_restantes > 0:
            if cantidad_niveles > 2:
                indice_nivel_elegido = random.randint(1, cantidad_niveles - 2)
            else:
                indice_nivel_elegido = 0
            tamanos_de_niveles[indice_nivel_elegido] = tamanos_de_niveles[indice_nivel_elegido] + 1
            nodos_restantes = nodos_restantes - 1

        return tamanos_de_niveles

    def generar_grafo_aleatorio(self):
        cantidad_niveles = self.determinar_cantidad_de_niveles()
        tamanos_de_niveles = self.repartir_nodos_en_niveles(cantidad_niveles)

        nombres_disponibles = list(self.grafo.nombres_nodos)
        random.shuffle(nombres_disponibles)

        niveles_de_nombres = []
        indice_actual = 0
        for tamano in tamanos_de_niveles:
            grupo_de_nombres = nombres_disponibles[indice_actual: indice_actual + tamano]
            niveles_de_nombres.append(grupo_de_nombres)
            indice_actual = indice_actual + tamano

        indice_nivel = 0
        while indice_nivel < len(niveles_de_nombres) - 1:
            nivel_actual = niveles_de_nombres[indice_nivel]
            nivel_siguiente = niveles_de_nombres[indice_nivel + 1]
            for nodo_origen in nivel_actual:
                nodo_destino = random.choice(nivel_siguiente)
                capacidad = random.randint(CAPACIDAD_MINIMA, CAPACIDAD_MAXIMA)
                self.grafo.agregar_arista(nodo_origen, nodo_destino, capacidad)
            indice_nivel = indice_nivel + 1

        indice_nivel = 1
        while indice_nivel < len(niveles_de_nombres):
            nivel_actual = niveles_de_nombres[indice_nivel]
            nivel_anterior = niveles_de_nombres[indice_nivel - 1]
            for nodo_destino in nivel_actual:
                ya_tiene_entrada = False
                for nodo_origen_posible in nivel_anterior:
                    if self.grafo.existe_arista(nodo_origen_posible, nodo_destino):
                        ya_tiene_entrada = True
                if ya_tiene_entrada == False:
                    nodo_origen = random.choice(nivel_anterior)
                    capacidad = random.randint(CAPACIDAD_MINIMA, CAPACIDAD_MAXIMA)
                    self.grafo.agregar_arista(nodo_origen, nodo_destino, capacidad)
            indice_nivel = indice_nivel + 1

        indice_nivel_origen = 0
        while indice_nivel_origen < len(niveles_de_nombres):
            indice_nivel_destino = indice_nivel_origen + 1
            while indice_nivel_destino < len(niveles_de_nombres):
                for nodo_origen in niveles_de_nombres[indice_nivel_origen]:
                    for nodo_destino in niveles_de_nombres[indice_nivel_destino]:
                        probabilidad = random.random()
                        if probabilidad < PROBABILIDAD_ARISTA_EXTRA:
                            if self.grafo.existe_arista(nodo_origen, nodo_destino) == False:
                                capacidad = random.randint(CAPACIDAD_MINIMA, CAPACIDAD_MAXIMA)
                                self.grafo.agregar_arista(nodo_origen, nodo_destino, capacidad)
                indice_nivel_destino = indice_nivel_destino + 1
            indice_nivel_origen = indice_nivel_origen + 1

    def mostrar_pantalla_manual(self):
        self.limpiar_contenedor()
        self.contenedor.configure(bg=COLOR_FONDO_CLARO)

        self.crear_boton_atras(self.contenedor, self.mostrar_pantalla_configuracion)

        titulo = tk.Label(self.contenedor, text="Construccion Manual del Grafo", font=("Arial", 16, "bold"))
        titulo.pack(pady=10)

        marco_formulario = tk.Frame(self.contenedor)
        marco_formulario.pack(pady=10)

        etiqueta_origen = tk.Label(marco_formulario, text="Nodo origen:")
        etiqueta_origen.grid(row=0, column=0, padx=5, pady=5)

        self.combo_origen = ttk.Combobox(marco_formulario, values=self.grafo.nombres_nodos, width=8, state="readonly")
        self.combo_origen.grid(row=0, column=1, padx=5, pady=5)

        etiqueta_destino = tk.Label(marco_formulario, text="Nodo destino:")
        etiqueta_destino.grid(row=0, column=2, padx=5, pady=5)

        self.combo_destino = ttk.Combobox(marco_formulario, values=self.grafo.nombres_nodos, width=8, state="readonly")
        self.combo_destino.grid(row=0, column=3, padx=5, pady=5)

        etiqueta_capacidad = tk.Label(marco_formulario, text="Capacidad:")
        etiqueta_capacidad.grid(row=0, column=4, padx=5, pady=5)

        self.entrada_capacidad = tk.Entry(marco_formulario, width=8)
        self.entrada_capacidad.grid(row=0, column=5, padx=5, pady=5)

        boton_agregar = tk.Button(marco_formulario, text="Agregar arista", command=self.agregar_arista_manual)
        boton_agregar.grid(row=0, column=6, padx=10, pady=5)

        etiqueta_lista = tk.Label(self.contenedor, text="Aristas agregadas:")
        etiqueta_lista.pack(pady=(10, 0))

        self.lista_aristas = tk.Listbox(self.contenedor, width=60, height=12)
        self.lista_aristas.pack(pady=10)

        for clave in self.grafo.capacidades.keys():
            origen_existente = clave[0]
            destino_existente = clave[1]
            capacidad_existente = self.grafo.capacidades[clave]
            texto_existente = origen_existente + " -> " + destino_existente + "   (capacidad = " + str(capacidad_existente) + ")"
            self.lista_aristas.insert("end", texto_existente)

        marco_botones = tk.Frame(self.contenedor)
        marco_botones.pack(pady=10)

        boton_eliminar = tk.Button(marco_botones, text="Eliminar seleccionada", command=self.eliminar_arista_manual)
        boton_eliminar.pack(side="left", padx=10)

        boton_finalizar = tk.Button(marco_botones, text="Finalizar Grafo", command=self.finalizar_grafo_manual, font=("Arial", 11, "bold"))
        boton_finalizar.pack(side="left", padx=10)

    def agregar_arista_manual(self):
        origen = self.combo_origen.get()
        destino = self.combo_destino.get()
        texto_capacidad = self.entrada_capacidad.get().strip()

        if origen == "" or destino == "":
            messagebox.showerror("Error", "Debe seleccionar el nodo origen y el nodo destino.")
            return

        if origen == destino:
            messagebox.showerror("Error", "El nodo origen y el nodo destino no pueden ser iguales.")
            return

        if texto_capacidad.isdigit() == False:
            messagebox.showerror("Error", "La capacidad debe ser un numero entero positivo.")
            return

        capacidad = int(texto_capacidad)
        if capacidad <= 0:
            messagebox.showerror("Error", "La capacidad debe ser mayor a cero.")
            return

        if self.grafo.existe_arista(origen, destino):
            messagebox.showerror("Error", "Esa arista ya fue agregada.")
            return

        self.grafo.agregar_arista(origen, destino, capacidad)
        texto_mostrado = origen + " -> " + destino + "   (capacidad = " + str(capacidad) + ")"
        self.lista_aristas.insert("end", texto_mostrado)

    def eliminar_arista_manual(self):
        seleccion = self.lista_aristas.curselection()
        if len(seleccion) == 0:
            messagebox.showerror("Error", "Debe seleccionar una arista de la lista para eliminarla.")
            return

        indice = seleccion[0]
        texto = self.lista_aristas.get(indice)
        primera_parte = texto.split(" -> ")
        origen = primera_parte[0]
        segunda_parte = primera_parte[1]
        destino = segunda_parte.split("   (")[0]

        self.grafo.eliminar_arista(origen, destino)
        self.lista_aristas.delete(indice)

    def finalizar_grafo_manual(self):
        if len(self.grafo.capacidades) == 0:
            messagebox.showerror("Error", "Debe agregar al menos una arista antes de continuar.")
            return

        if self.grafo.tiene_ciclo():
            messagebox.showerror(
                "Ciclo detectado",
                "El grafo ingresado contiene al menos un ciclo.\n\n"
                "El algoritmo de Ford-Fulkerson requiere que la red de flujo "
                "no contenga ciclos entre las aristas ingresadas.\n\n"
                "Por favor elimine o corrija la arista responsable e intente nuevamente."
            )
            return

        self.mostrar_pantalla_seleccion()

    def construir_grafo_networkx(self):
        grafo_dibujo = nx.DiGraph()
        for nombre in self.grafo.nombres_nodos:
            grafo_dibujo.add_node(nombre)
        for clave in self.grafo.capacidades.keys():
            origen = clave[0]
            destino = clave[1]
            grafo_dibujo.add_edge(origen, destino)
        return grafo_dibujo

    def calcular_niveles_topologicos(self, grafo_dibujo):

        grados_entrada = {}
        for nodo in grafo_dibujo.nodes():
            grados_entrada[nodo] = 0
        for arista in grafo_dibujo.edges():
            destino = arista[1]
            grados_entrada[destino] = grados_entrada[destino] + 1

        nivel_de_nodo = {}
        cola = deque()
        for nodo in grafo_dibujo.nodes():
            if grados_entrada[nodo] == 0:
                nivel_de_nodo[nodo] = 0
                cola.append(nodo)

        grados_entrada_restante = dict(grados_entrada)
        while len(cola) > 0:
            nodo_actual = cola.popleft()
            vecinos = list(grafo_dibujo.successors(nodo_actual))
            for vecino in vecinos:
                nivel_propuesto = nivel_de_nodo[nodo_actual] + 1
                if vecino not in nivel_de_nodo:
                    nivel_de_nodo[vecino] = nivel_propuesto
                elif nivel_propuesto > nivel_de_nodo[vecino]:
                    nivel_de_nodo[vecino] = nivel_propuesto

                grados_entrada_restante[vecino] = grados_entrada_restante[vecino] - 1
                if grados_entrada_restante[vecino] == 0:
                    cola.append(vecino)

        for nodo in grafo_dibujo.nodes():
            if nodo not in nivel_de_nodo:
                nivel_de_nodo[nodo] = 0

        return nivel_de_nodo

    def construir_posiciones_por_niveles(self, grafo_dibujo, nivel_de_nodo):
        nodos_por_nivel = {}
        for nodo in grafo_dibujo.nodes():
            nivel = nivel_de_nodo[nodo]
            if nivel not in nodos_por_nivel:
                nodos_por_nivel[nivel] = []
            nodos_por_nivel[nivel].append(nodo)

        posiciones = {}
        niveles_ordenados = sorted(nodos_por_nivel.keys())
        for nivel in niveles_ordenados:
            nodos_en_nivel = nodos_por_nivel[nivel]
            cantidad_en_nivel = len(nodos_en_nivel)
            indice = 0
            while indice < cantidad_en_nivel:
                nodo = nodos_en_nivel[indice]
                coordenada_x = nivel * 2.6
                coordenada_y = (indice - (cantidad_en_nivel - 1) / 2.0) * 1.9
                posiciones[nodo] = (coordenada_x, coordenada_y)
                indice = indice + 1

        return posiciones

    def dibujar_grafo(self, marco_padre, mostrar_flujo=False, aristas_corte=None, conjunto_alcanzable=None):
        grafo_dibujo = self.construir_grafo_networkx()

        if self.posiciones_layout is None:
            nivel_de_nodo = self.calcular_niveles_topologicos(grafo_dibujo)
            self.posiciones_layout = self.construir_posiciones_por_niveles(grafo_dibujo, nivel_de_nodo)

        figura = plt.Figure(figsize=(9.5, 6.4), dpi=100)
        ejes = figura.add_subplot(111)

        colores_nodos = []
        for nombre in grafo_dibujo.nodes():
            if conjunto_alcanzable is not None and nombre in conjunto_alcanzable:
                colores_nodos.append("#a8d5a2")
            elif nombre == self.nodo_fuente_final:
                colores_nodos.append("#f4b183")
            elif nombre == self.nodo_sumidero_final:
                colores_nodos.append("#9dc3e6")
            else:
                colores_nodos.append("#d9d9d9")

        nx.draw_networkx_nodes(
            grafo_dibujo, self.posiciones_layout, ax=ejes,
            node_color=colores_nodos, node_size=700, edgecolors="black"
        )
        nx.draw_networkx_labels(grafo_dibujo, self.posiciones_layout, ax=ejes, font_size=9)

        colores_aristas = []
        anchos_aristas = []
        for arista in grafo_dibujo.edges():
            if aristas_corte is not None and arista in aristas_corte:
                colores_aristas.append("red")
                anchos_aristas.append(2.6)
            else:
                colores_aristas.append("black")
                anchos_aristas.append(1.2)

        nx.draw_networkx_edges(
            grafo_dibujo, self.posiciones_layout, ax=ejes,
            edge_color=colores_aristas, width=anchos_aristas,
            arrowsize=14, connectionstyle="arc3,rad=0.05", node_size=700
        )

        etiquetas_aristas = {}
        for clave in self.grafo.capacidades.keys():
            origen = clave[0]
            destino = clave[1]
            capacidad = self.grafo.capacidades[clave]
            if mostrar_flujo:
                flujo = self.grafo.flujos[clave]
                etiquetas_aristas[clave] = str(flujo) + " / " + str(capacidad)
            else:
                etiquetas_aristas[clave] = str(capacidad)

        nx.draw_networkx_edge_labels(
            grafo_dibujo, self.posiciones_layout, edge_labels=etiquetas_aristas,
            ax=ejes, font_size=8
        )

        ejes.set_axis_off()

        lienzo = FigureCanvasTkAgg(figura, master=marco_padre)
        lienzo.draw()
        widget_lienzo = lienzo.get_tk_widget()
        widget_lienzo.pack(fill="both", expand=True)
        return widget_lienzo

    def mostrar_pantalla_seleccion(self):
        self.limpiar_contenedor()
        self.posiciones_layout = None

        self.crear_boton_atras(self.contenedor, self.regresar_desde_seleccion)

        titulo = tk.Label(self.contenedor, text="Seleccion de Vertice(s) Fuente y Sumidero", font=("Arial", 16, "bold"))
        titulo.pack(pady=10)

        marco_principal = tk.Frame(self.contenedor)
        marco_principal.pack(fill="both", expand=True, padx=10, pady=10)

        marco_grafo = tk.Frame(marco_principal)
        marco_grafo.pack(side="left", fill="both", expand=True)
        self.dibujar_grafo(marco_grafo)

        marco_lateral = tk.Frame(marco_principal)
        marco_lateral.pack(side="right", fill="y", padx=10)

        etiqueta_fuentes = tk.Label(marco_lateral, text="Vertice(s) fuente\n(puede seleccionar varios):", justify="left")
        etiqueta_fuentes.pack(anchor="w")

        self.lista_fuentes = tk.Listbox(marco_lateral, selectmode="multiple", height=8, exportselection=False)
        for nombre in self.grafo.nombres_nodos:
            self.lista_fuentes.insert("end", nombre)
        self.lista_fuentes.pack(pady=5)

        etiqueta_sumideros = tk.Label(marco_lateral, text="Vertice(s) sumidero\n(puede seleccionar varios):", justify="left")
        etiqueta_sumideros.pack(anchor="w")

        self.lista_sumideros = tk.Listbox(marco_lateral, selectmode="multiple", height=8, exportselection=False)
        for nombre in self.grafo.nombres_nodos:
            self.lista_sumideros.insert("end", nombre)
        self.lista_sumideros.pack(pady=5)

        nota = tk.Label(
            marco_lateral,
            text="Si selecciona mas de una fuente o\nmas de un sumidero, el sistema\ncreara un nodo ficticio automaticamente.",
            justify="left", fg="#555555", font=("Arial", 9)
        )
        nota.pack(pady=10)

        boton_continuar = tk.Button(marco_lateral, text="Continuar", command=self.procesar_seleccion_fuente_sumidero, font=("Arial", 11, "bold"))
        boton_continuar.pack(pady=10)

    def regresar_desde_seleccion(self):
        modo = self.modo_construccion.get()
        if modo == "manual":
            self.mostrar_pantalla_manual()
        else:
            self.mostrar_pantalla_configuracion()

    def calcular_capacidad_saliente(self, nodo):
        total = 0
        for clave in self.grafo.capacidades.keys():
            origen = clave[0]
            if origen == nodo:
                total = total + self.grafo.capacidades[clave]
        return total

    def calcular_capacidad_entrante(self, nodo):
        total = 0
        for clave in self.grafo.capacidades.keys():
            destino = clave[1]
            if destino == nodo:
                total = total + self.grafo.capacidades[clave]
        return total

    def procesar_seleccion_fuente_sumidero(self):
        indices_fuentes = self.lista_fuentes.curselection()
        indices_sumideros = self.lista_sumideros.curselection()

        if len(indices_fuentes) == 0 or len(indices_sumideros) == 0:
            messagebox.showerror("Error", "Debe seleccionar al menos un vertice fuente y al menos un vertice sumidero.")
            return

        fuentes = []
        for indice in indices_fuentes:
            fuentes.append(self.grafo.nombres_nodos[indice])

        sumideros = []
        for indice in indices_sumideros:
            sumideros.append(self.grafo.nombres_nodos[indice])

        conjunto_fuentes = set(fuentes)
        conjunto_sumideros = set(sumideros)
        interseccion = conjunto_fuentes.intersection(conjunto_sumideros)
        if len(interseccion) > 0:
            messagebox.showerror("Error", "Un mismo vertice no puede ser fuente y sumidero al mismo tiempo.")
            return

        self.fuentes_seleccionadas = fuentes
        self.sumideros_seleccionados = sumideros

        self.respaldo_capacidades = dict(self.grafo.capacidades)
        self.respaldo_flujos = dict(self.grafo.flujos)
        self.respaldo_nombres_nodos = list(self.grafo.nombres_nodos)

        if len(fuentes) == 1:
            self.nodo_fuente_final = fuentes[0]
        else:
            nombre_ficticio = "Origen_Ficticio"
            self.grafo.agregar_nodo_ficticio(nombre_ficticio)
            for fuente in fuentes:
                capacidad_total = self.calcular_capacidad_saliente(fuente)
                if capacidad_total == 0:
                    capacidad_total = CAPACIDAD_MAXIMA
                self.grafo.agregar_arista(nombre_ficticio, fuente, capacidad_total)
            self.nodo_fuente_final = nombre_ficticio

        if len(sumideros) == 1:
            self.nodo_sumidero_final = sumideros[0]
        else:
            nombre_ficticio = "Destino_Ficticio"
            self.grafo.agregar_nodo_ficticio(nombre_ficticio)
            for sumidero in sumideros:
                capacidad_total = self.calcular_capacidad_entrante(sumidero)
                if capacidad_total == 0:
                    capacidad_total = CAPACIDAD_MAXIMA
                self.grafo.agregar_arista(sumidero, nombre_ficticio, capacidad_total)
            self.nodo_sumidero_final = nombre_ficticio

        self.posiciones_layout = None
        self.solucionador = FordFulkerson(self.grafo, self.nodo_fuente_final, self.nodo_sumidero_final)
        self.mostrar_pantalla_ejecucion()

    def mostrar_pantalla_ejecucion(self):
        self.limpiar_contenedor()

        if hasattr(self, "boton_resultado_final"):
            delattr(self, "boton_resultado_final")

        self.crear_boton_atras(self.contenedor, self.regresar_desde_ejecucion)

        titulo_texto = "Ejecucion del Algoritmo  |  Fuente: " + self.nodo_fuente_final + "   Sumidero: " + self.nodo_sumidero_final
        titulo = tk.Label(self.contenedor, text=titulo_texto, font=("Arial", 14, "bold"))
        titulo.pack(pady=10)

        marco_principal = tk.Frame(self.contenedor)
        marco_principal.pack(fill="both", expand=True, padx=10, pady=5)

        self.marco_grafo_ejecucion = tk.Frame(marco_principal)
        self.marco_grafo_ejecucion.pack(side="left", fill="both", expand=True)
        self.dibujar_grafo(self.marco_grafo_ejecucion, mostrar_flujo=True)

        marco_lateral = tk.Frame(marco_principal)
        marco_lateral.pack(side="right", fill="y", padx=10)

        self.etiqueta_flujo_total = tk.Label(marco_lateral, text="Flujo total acumulado: " + str(self.solucionador.flujo_total), font=("Arial", 12, "bold"))
        self.etiqueta_flujo_total.pack(pady=10)

        etiqueta_registro = tk.Label(marco_lateral, text="Registro de ejecucion:")
        etiqueta_registro.pack(anchor="w")

        self.area_registro = scrolledtext.ScrolledText(marco_lateral, width=48, height=24)
        self.area_registro.pack(pady=5)

        for paso_anterior in self.solucionador.historial_caminos:
            self.area_registro.insert("end", self.formatear_linea_paso(paso_anterior))
        if self.solucionador.terminado:
            self.area_registro.insert("end", "No se encontraron mas caminos de aumento.\nEl algoritmo ha finalizado.\n\n")
        self.area_registro.see("end")

        marco_botones = tk.Frame(marco_lateral)
        marco_botones.pack(pady=10)

        boton_siguiente = tk.Button(marco_botones, text="Siguiente Paso", command=self.ejecutar_siguiente_paso)
        boton_siguiente.pack(side="left", padx=5)

        boton_completo = tk.Button(marco_botones, text="Ejecutar Todo", command=self.ejecutar_todo)
        boton_completo.pack(side="left", padx=5)

        if self.solucionador.terminado:
            self.mostrar_boton_resultado_final()

    def regresar_desde_ejecucion(self):
        if self.respaldo_capacidades is not None:
            self.grafo.capacidades = dict(self.respaldo_capacidades)
            self.grafo.flujos = dict(self.respaldo_flujos)
            self.grafo.nombres_nodos = list(self.respaldo_nombres_nodos)

        self.nodo_fuente_final = None
        self.nodo_sumidero_final = None
        self.solucionador = None
        self.posiciones_layout = None
        self.mostrar_pantalla_seleccion()

    def formatear_linea_paso(self, resultado_paso):
        camino_texto = " -> ".join(resultado_paso["camino"])
        linea = "Camino de aumento encontrado:\n   " + camino_texto + "\n"
        linea = linea + "Capacidad residual minima (cuello de botella): " + str(resultado_paso["capacidad"]) + "\n"
        linea = linea + "Flujo acumulado hasta el momento: " + str(resultado_paso["flujo_acumulado"]) + "\n\n"
        return linea

    def ejecutar_siguiente_paso(self):
        if self.solucionador.terminado:
            messagebox.showinfo("Informacion", "El algoritmo ya finalizo. Presione 'Ver Resultado Final'.")
            return

        resultado_paso = self.solucionador.ejecutar_un_paso()

        if resultado_paso is None:
            self.area_registro.insert("end", "No se encontraron mas caminos de aumento.\nEl algoritmo ha finalizado.\n\n")
            self.area_registro.see("end")
            self.mostrar_boton_resultado_final()
            return

        linea_registro = self.formatear_linea_paso(resultado_paso)
        self.area_registro.insert("end", linea_registro)
        self.area_registro.see("end")

        self.etiqueta_flujo_total.config(text="Flujo total acumulado: " + str(self.solucionador.flujo_total))
        self.redibujar_grafo_ejecucion()

    def redibujar_grafo_ejecucion(self):
        lista_hijos = self.marco_grafo_ejecucion.winfo_children()
        for hijo in lista_hijos:
            hijo.destroy()
        self.dibujar_grafo(self.marco_grafo_ejecucion, mostrar_flujo=True)

    def ejecutar_todo(self):
        while self.solucionador.terminado == False:
            resultado_paso = self.solucionador.ejecutar_un_paso()
            if resultado_paso is None:
                break
            linea_registro = self.formatear_linea_paso(resultado_paso)
            self.area_registro.insert("end", linea_registro)

        self.area_registro.insert("end", "No se encontraron mas caminos de aumento.\nEl algoritmo ha finalizado.\n\n")
        self.area_registro.see("end")

        self.etiqueta_flujo_total.config(text="Flujo total acumulado: " + str(self.solucionador.flujo_total))
        self.redibujar_grafo_ejecucion()
        self.mostrar_boton_resultado_final()

    def mostrar_boton_resultado_final(self):
        if hasattr(self, "boton_resultado_final"):
            return

        self.boton_resultado_final = tk.Button(
            self.contenedor, text="Ver Resultado Final",
            command=self.mostrar_pantalla_resultado,
            font=("Arial", 11, "bold"), bg="#70ad47", fg="white"
        )
        self.boton_resultado_final.pack(pady=10)

    def mostrar_pantalla_resultado(self):
        self.limpiar_contenedor()

        self.crear_boton_atras(self.contenedor, self.mostrar_pantalla_ejecucion)

        titulo = tk.Label(self.contenedor, text="Resultado Final: Flujo Maximo y Corte Minimo", font=("Arial", 16, "bold"))
        titulo.pack(pady=10)

        aristas_corte, conjunto_alcanzable = self.solucionador.calcular_corte_minimo()

        marco_principal = tk.Frame(self.contenedor)
        marco_principal.pack(fill="both", expand=True, padx=10, pady=10)

        marco_grafo = tk.Frame(marco_principal)
        marco_grafo.pack(side="left", fill="both", expand=True)
        self.dibujar_grafo(marco_grafo, mostrar_flujo=True, aristas_corte=aristas_corte, conjunto_alcanzable=conjunto_alcanzable)

        marco_lateral = tk.Frame(marco_principal)
        marco_lateral.pack(side="right", fill="y", padx=10)

        area_resumen = scrolledtext.ScrolledText(marco_lateral, width=52, height=32)
        area_resumen.pack(pady=5)

        texto_resumen = "VALOR DEL FLUJO MAXIMO: " + str(self.solucionador.flujo_total) + "\n\n"

        texto_resumen = texto_resumen + "CAMINOS DE AUMENTO UTILIZADOS:\n"
        contador = 1
        for paso in self.solucionador.historial_caminos:
            camino_texto = " -> ".join(paso["camino"])
            texto_resumen = texto_resumen + str(contador) + ". " + camino_texto + "   (cantidad = " + str(paso["capacidad"]) + ")\n"
            contador = contador + 1

        texto_resumen = texto_resumen + "\nFLUJO FINAL EN CADA ARISTA:\n"
        for clave in self.grafo.capacidades.keys():
            origen = clave[0]
            destino = clave[1]
            capacidad = self.grafo.capacidades[clave]
            flujo = self.grafo.flujos[clave]
            texto_resumen = texto_resumen + origen + " -> " + destino + " :  " + str(flujo) + " / " + str(capacidad) + "\n"

        texto_resumen = texto_resumen + "\nCORTE MINIMO (aristas que lo componen):\n"
        suma_capacidades_corte = 0
        for clave in aristas_corte:
            origen = clave[0]
            destino = clave[1]
            capacidad = self.grafo.capacidades[clave]
            suma_capacidades_corte = suma_capacidades_corte + capacidad
            texto_resumen = texto_resumen + origen + " -> " + destino + "   (capacidad = " + str(capacidad) + ")\n"

        texto_resumen = texto_resumen + "\nSuma de capacidades del corte minimo: " + str(suma_capacidades_corte) + "\n"
        texto_resumen = texto_resumen + "Esta suma coincide con el flujo maximo, lo cual verifica\n"
        texto_resumen = texto_resumen + "el teorema de flujo maximo - corte minimo.\n"

        area_resumen.insert("end", texto_resumen)
        area_resumen.config(state="disabled")

if __name__ == "__main__":
    aplicacion = AplicacionFlujoMaximo()
    aplicacion.mainloop()
