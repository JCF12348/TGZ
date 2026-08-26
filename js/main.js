let bleDevice, gattServer;
let epdService, epdCharacteristic, epdNotifyCharacteristic;
let legacyEpdService, legacyEpdCharacteristic, legacyEpdNotifyCharacteristic;
let nrfEpdService, nrfEpdCharacteristic, nrfEpdVersionCharacteristic;
let startTime, msgIndex;
let canvas, ctx, textDecoder;
let paintManager, cropManager;
let bleWriteChain = Promise.resolve();
let currentPinsValue = '';
let ditherSourceImageData = null;
let ditherPreviewActive = false;
let pageExitDisconnecting = false;
let slotState = { count: 0, pageStart: 0, pageCount: 0, usedMask: 0, selected: null, flashSize: 0, fingerprints: [] };
let slotReadState = null;
let slotImageCache = new Map();
let slotImageCacheScope = '';
let slotPreviewPending = new Set();
let slotProtocolV2 = false;
let rleSupport = false;
let slotStreamSupport = false;
let clockFontSupport = false;
let clockFontVersion = 2;
let clockFontBusy = false;
let clockFontSourceCanvas = null;
let imageTransferActive = false;
let imageRefreshPending = false;
let imageRefreshTimer = null;
let imageCompletionKind = 'refresh';
let imagePrepareWait = null;
let slotActionPending = false;
let slotActionTimer = null;
let slotReadTimer = null;
let slotEraseAllPending = false;
let displayErrorActive = false;
let otaPackage = null;
let otaClient = null;
let otaBusy = false;
let otaPhase = 'idle';
let otaNextLogPercent = 10;
let reconnectActive = false;
let deviceInitPending = false;
let deviceInitRetryTimer = null;
let customCalendarFontFamily = '';
let calendarStyleRenderTimer = null;
let calendarStyleImageActive = false;
let ledColorWriteTimer = null;
let tgzRx = null;
let tgzTxSequence = 0;
let tgzPacketLengthIndex = 0;
let tgzNoResponseRemaining = 50;
let tgzFastWriteEnabled = true;
let tgzResponseWaiters = [];
let tgzPanelId = 0;
let tgzStorageAvailable = false;
let tgzStorageFreeSlots = 0;
let tgzTransferProgressFrame = null;
let tgzTransferTargetProgress = 0;
let tgzImageErrorResponse = null;
let nativeNrfMtu = 20;
let nativeNrfNoResponseRemaining = 20;
let nativeNrfWaiters = [];

const MAX_SLOT_IMAGE_SIZE = 1024 * 1024;
const DEFAULT_SLOT_READ_RAW_CHUNK_SIZE = 256;
const SLOT_READ_TIMEOUT_MS = 5000;
const SLOT_READ_INFO_TIMEOUT_MS = 8000;
const SLOT_CHUNK_MAX_RETRIES = 2;
const SLOT_PAGE_SIZE = 18;
const IMAGE_REFRESH_TIMEOUT_MS = 95000;
const SLOT_IMAGE_CACHE_PREFIX = 'epd-slot-preview-v2:';
const SLOT_PREVIEW_MAX_EDGE = 480;
const SLOT_PREVIEW_JPEG_QUALITY = 0.88;
const RECONNECT_MAX_ATTEMPTS = 3;
const RECONNECT_RETRY_DELAY_MS = 600;
const DEVICE_INIT_RETRY_DELAY_MS = 1000;
const LED_COLOR_WRITE_DELAY_MS = 100;
const CLOCK_FONT_V1_GLYPH_WIDTH = 32;
const CLOCK_FONT_V2_GLYPH_WIDTH = 40;
const CLOCK_FONT_V2_COLON_WIDTH = 8;
let CLOCK_FONT_GLYPH_WIDTH = CLOCK_FONT_V2_GLYPH_WIDTH;
const CLOCK_FONT_GLYPH_HEIGHT = 80;
const CLOCK_FONT_GLYPHS = '0123456789:';
let CLOCK_FONT_GLYPH_BYTES = CLOCK_FONT_GLYPH_WIDTH * CLOCK_FONT_GLYPH_HEIGHT / 8;
let CLOCK_FONT_DATA_SIZE = 4080;

const PAGE_BACKGROUND_STORAGE_KEY = 'epdCustomPageBackground';
const PAGE_BACKGROUND_SETTINGS_STORAGE_KEY = 'epdCustomPageBackgroundSettings';
const UI_OPACITY_STORAGE_KEY = 'epdUiOpacity';
const GLASS_CLARITY_STORAGE_KEY = 'epdGlassClarity';
const PAGE_BACKGROUND_MAX_SIZE = 1920;
const PAGE_BACKGROUND_QUALITY = 0.82;
const DEFAULT_UI_OPACITY = 0.88;
const DEFAULT_GLASS_CLARITY = 0;
const MAX_GLASS_BLUR = 24;
const DEFAULT_PAGE_BACKGROUND_SETTINGS = {
  fit: 'contain',
  zoom: 1,
  offsetX: 0,
  offsetY: 0,
  rotate: 0,
  flipX: false,
  flipY: false,
  brightness: 1,
  contrast: 1,
  saturation: 1,
  mask: 0.22
};

const NRF_EPD_SERVICE_UUID = '62750001-d828-918d-fb46-b6c11c675aec';
const NRF_EPD_CHARACTERISTIC_UUID = '62750002-d828-918d-fb46-b6c11c675aec';
const NRF_EPD_VERSION_UUID = '62750003-d828-918d-fb46-b6c11c675aec';
const EPD_SERVICE_UUID = '0000ffff-0000-1000-8000-00805f9b34fb';
const EPD_WRITE_UUID = '0000ff01-0000-1000-8000-00805f9b34fb';
const EPD_NOTIFY_UUID = '0000ff02-0000-1000-8000-00805f9b34fb';
const TGZ_WIDTH = 760;
const TGZ_HEIGHT = 528;
const TGZ_RLE_CHUNK_SIZE = 1024;
const TGZ_PACKET_LENGTHS = [244, 180, 120, 64, 20];
const TGZ_WRITE_PACING_MS = 4;
const TGZ_WRITE_RESPONSE_INTERVAL = 50;
const NATIVE_NRF_WRITE_PACING_MS = 4;
const NATIVE_NRF_WRITE_RESPONSE_INTERVAL = 20;
const TGZ_PANEL_NAMES = {
  1: 'SE0398 A0',
  2: 'SE0398 New-A1',
  3: '3.65 英寸六色 E6',
  4: '3.98 英寸六色 E6',
  5: '3.68 英寸六色 E6',
};

const EpdCmd = {
  SET_PINS: 0x00,
  INIT: 0x01,
  CLEAR: 0x02,
  SEND_CMD: 0x03,
  SEND_DATA: 0x04,
  REFRESH: 0x05,
  SLEEP: 0x06,

  SET_TIME: 0x20,
  SET_WEEK_START: 0x21,
  SET_LED: 0x93,

  WRITE_IMG: 0x30, // v1.6
  SET_SLOT: 0x31,
  FREE_SLOT: 0x32,
  SET_SLIDE: 0x33,
  GET_IMAGE: 0x34,
  GET_SLOTS: 0x35,
  SET_FONT: 0x36,

  SET_CONFIG: 0x90,
  SYS_RESET: 0x91,
  SYS_SLEEP: 0x92,
  CFG_ERASE: 0x99,
};

const LEGACY_EPD_CONFIG_SIZES = [14, 15, 16];
const EPD_CONFIG_SIZE = 19;
const LED_CONTROL_MIN_VERSION = 0x40;
let firmwareVersion = { label: '未知', ledControl: false, directImagePrepare: false, outdated: true };

const canvasSizes = [
  { name: 'TGZ_760_528', width: 760, height: 528 },
  { name: '1.54_152_152', width: 152, height: 152 },
  { name: '1.54_200_200', width: 200, height: 200 },
  { name: '2.13_212_104', width: 212, height: 104 },
  { name: '2.13_250_122', width: 250, height: 122 },
  { name: '2.13_128_250', width: 128, height: 250 },
  { name: '2.66_296_152', width: 296, height: 152 },
  { name: '2.9_296_128', width: 296, height: 128 },
  { name: '2.9_384_168', width: 384, height: 168 },
  { name: '3.5_384_184', width: 384, height: 184 },
  { name: '3.7_416_240', width: 416, height: 240 },
  { name: '3.97_800_480', width: 800, height: 480 },
  { name: '3.98_768_552', width: 768, height: 552 },
  { name: '3.98_800_600', width: 800, height: 600 },
  { name: '3.87_800_480', width: 800, height: 480 },
  { name: '9.7_960_680', width: 960, height: 680 },
  { name: '4.2_400_300', width: 400, height: 300 },
  { name: '5.65_600_448', width: 600, height: 448 },
  { name: '5.79_792_272', width: 792, height: 272 },
  { name: '5.83_600_448', width: 600, height: 448 },
  { name: '5.83_648_480', width: 648, height: 480 },
  { name: '7.5_640_384', width: 640, height: 384 },
  { name: '7.5_800_480', width: 800, height: 480 },
  { name: '7.5_880_528', width: 880, height: 528 },
  { name: '10.2_960_640', width: 960, height: 640 },
  { name: '10.85_1360_480', width: 1360, height: 480 },
  { name: '11.6_960_640', width: 960, height: 640 },
  { name: '4E_600_400', width: 600, height: 400 },
  { name: '7.3E6', width: 480, height: 800 }
];

function hex2bytes(hex) {
  for (var bytes = [], c = 0; c < hex.length; c += 2)
    bytes.push(parseInt(hex.substr(c, 2), 16));
  return new Uint8Array(bytes);
}

function bytes2hex(data) {
  return new Uint8Array(data).reduce(
    function (memo, i) {
      return memo + ("0" + i.toString(16)).slice(-2);
    }, "");
}

function parseFirmwareVersion(value) {
  const bytes = new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
  const text = new TextDecoder().decode(bytes).replace(/\0+$/, '');
  const semantic = /^V(\d+)\.(\d+)$/.exec(text);
  if (semantic) {
    const major = parseInt(semantic[1], 10);
    const minor = parseInt(semantic[2], 10);
    const currentOrNewer = major > 1 || (major === 1 && minor >= 8);
    return {
      label: text,
      ledControl: currentOrNewer,
      directImagePrepare: major > 1 || (major === 1 && minor >= 36),
      outdated: !currentOrNewer,
    };
  }

  const legacy = bytes.length > 0 ? bytes[0] : 0;
  return {
    label: `0x${legacy.toString(16)}`,
    ledControl: legacy >= LED_CONTROL_MIN_VERSION,
    directImagePrepare: false,
    outdated: legacy < 0x16,
  };
}

function intToHex(intIn) {
  let stringOut = ("0000" + intIn.toString(16)).substr(-4)
  return stringOut.substring(2, 4) + stringOut.substring(0, 2);
}

function resetVariables(options = {}) {
  const clearLog = options.clearLog !== false;
  gattServer = null;
  epdService = null;
  epdCharacteristic = null;
  epdNotifyCharacteristic = null;
  legacyEpdService = null;
  legacyEpdCharacteristic = null;
  legacyEpdNotifyCharacteristic = null;
  nrfEpdService = null;
  nrfEpdCharacteristic = null;
  nrfEpdVersionCharacteristic = null;
  firmwareVersion = { label: '未知', ledControl: false, directImagePrepare: false, outdated: true };
  msgIndex = 0;
  bleWriteChain = Promise.resolve();
  currentPinsValue = '';
  slotState = { count: 0, pageStart: 0, pageCount: 0, usedMask: 0, selected: null, flashSize: 0, fingerprints: [] };
  if (slotReadTimer != null) clearTimeout(slotReadTimer);
  slotReadTimer = null;
  slotReadState = null;
  slotImageCache = new Map();
  slotImageCacheScope = '';
  slotProtocolV2 = false;
  slotPreviewPending = new Set();
  rleSupport = false;
  tgzRx = new MemobusClient.BlufiReassembler();
  tgzTxSequence = 0;
  tgzPacketLengthIndex = 0;
  tgzNoResponseRemaining = TGZ_WRITE_RESPONSE_INTERVAL;
  tgzFastWriteEnabled = true;
  tgzResponseWaiters.splice(0).forEach(waiter => {
    clearTimeout(waiter.timer);
    waiter.reject(new Error('连接已重置'));
  });
  tgzPanelId = 0;
  tgzStorageAvailable = false;
  tgzStorageFreeSlots = 0;
  tgzImageErrorResponse = null;
  nativeNrfMtu = 20;
  nativeNrfNoResponseRemaining = NATIVE_NRF_WRITE_RESPONSE_INTERVAL;
  nativeNrfWaiters.splice(0).forEach(waiter => {
    clearTimeout(waiter.timer);
    waiter.reject(new Error('连接已重置'));
  });
  slotStreamSupport = false;
  clockFontSupport = false;
  clockFontBusy = false;
  imageTransferActive = false;
  cancelImagePrepareWait();
  imageRefreshPending = false;
  imageCompletionKind = 'refresh';
  if (imageRefreshTimer != null) clearTimeout(imageRefreshTimer);
  imageRefreshTimer = null;
  slotActionPending = false;
  slotEraseAllPending = false;
  displayErrorActive = false;
  clearDeviceInitRetry();
  if (slotActionTimer != null) clearTimeout(slotActionTimer);
  slotActionTimer = null;
  renderSlotGrid();
  if (clearLog) document.getElementById("log").value = '';
}

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

function isGattBusyError(error) {
  const message = error && error.message ? error.message : '';
  return message.includes('GATT operation already in progress') ||
    message.includes('operation already in progress');
}

function queueBleWrite(task) {
  const run = bleWriteChain.catch(() => { }).then(task);
  bleWriteChain = run.catch(() => { });
  return run;
}

async function writeCharacteristicValue(characteristic, value, withResponse) {
  const bytes = value instanceof Uint8Array ? value : Uint8Array.from(value);
  if (withResponse && typeof characteristic.writeValueWithResponse === 'function')
    return characteristic.writeValueWithResponse(bytes);
  if (!withResponse && typeof characteristic.writeValueWithoutResponse === 'function')
    return characteristic.writeValueWithoutResponse(bytes);
  if (typeof characteristic.writeValue === 'function')
    return characteristic.writeValue(bytes);
  throw new Error('当前浏览器不支持蓝牙特征写入');
}

async function writeTgzPacket(characteristic, packet, preferFast) {
  if (preferFast) {
    try {
      await writeCharacteristicValue(characteristic, packet, false);
      return true;
    } catch (_) {
      await writeCharacteristicValue(characteristic, packet, true);
      return false;
    }
  }
  await writeCharacteristicValue(characteristic, packet, true);
  return false;
}

async function writeNativeNrfPayload(payload, preferFast = false) {
  if (!nrfEpdCharacteristic) throw new Error('nRF 原生传输特征不可用');
  const bytes = payload instanceof Uint8Array ? payload : Uint8Array.from(payload);

  return queueBleWrite(async () => {
    for (let retry = 0; retry < 8; retry++) {
      try {
        if (preferFast) {
          try {
            await writeCharacteristicValue(nrfEpdCharacteristic, bytes, false);
            return true;
          } catch (_) {
            await writeCharacteristicValue(nrfEpdCharacteristic, bytes, true);
            return false;
          }
        }
        await writeCharacteristicValue(nrfEpdCharacteristic, bytes, true);
        return false;
      } catch (error) {
        if (!isGattBusyError(error) || retry === 7) throw error;
        await sleep(10 + retry * 10);
      }
    }
    return false;
  });
}

async function writeGattPayload(payload, withResponse) {
  const bytes = Uint8Array.from(payload);

  for (let retry = 0; retry < 8; retry++) {
    try {
      await writeCharacteristicValue(epdCharacteristic, bytes, withResponse);

      if (!withResponse) await sleep(4);
      return;
    } catch (e) {
      if (!isGattBusyError(e) || retry == 7) throw e;
      await sleep(10 + retry * 10);
    }
  }
}

async function write(cmd, data, withResponse = true) {
  if (!epdCharacteristic) {
    addLog("服务不可用，请检查蓝牙连接");
    return false;
  }
  let payload = [cmd];
  if (data) {
    if (typeof data == 'string') data = hex2bytes(data);
    if (data instanceof Uint8Array) data = Array.from(data);
    payload.push(...data)
  }
  const isSlotChunkRequest = cmd === EpdCmd.GET_IMAGE && payload.length === 4;
  const isClockFontData = cmd === EpdCmd.SET_FONT && payload[1] === 1;
  if (cmd !== EpdCmd.WRITE_IMG && !isSlotChunkRequest && !isClockFontData) {
    const logPayload = cmd === EpdCmd.SET_LED
      ? payload.map(value => value.toString(16).padStart(2, '0')).join(' ')
      : bytes2hex(payload);
    addLog(logPayload, '⇑');
  }
  try {
    await queueBleWrite(() => writeGattPayload(payload, withResponse));
  } catch (e) {
    console.error(e);
    if (e.message) addLog("write: " + e.message);
    return false;
  }
  return true;
}

function isBleConnected() {
  return gattServer != null && gattServer.connected &&
    (nrfEpdCharacteristic != null || epdCharacteristic != null);
}

function formatSlotBytes(size) {
  if (size < 1024) return `${size} B`;
  if (size < 1024 * 1024) return `${(size / 1024).toFixed(1)} KB`;
  return `${(size / 1024 / 1024).toFixed(1)} MB`;
}

function toggleClockFontPanel() {
  const panel = document.getElementById('clockFontPanel');
  const button = document.getElementById('clockFontPanelToggle');
  panel.hidden = !panel.hidden;
  button.setAttribute('aria-expanded', String(!panel.hidden));
}

function setClockFontFormat(version) {
  clockFontVersion = version >= 2 ? 2 : 1;
  CLOCK_FONT_GLYPH_WIDTH = clockFontVersion >= 2 ? CLOCK_FONT_V2_GLYPH_WIDTH : CLOCK_FONT_V1_GLYPH_WIDTH;
  CLOCK_FONT_GLYPH_BYTES = CLOCK_FONT_GLYPH_WIDTH * CLOCK_FONT_GLYPH_HEIGHT / 8;
  CLOCK_FONT_DATA_SIZE = clockFontVersion >= 2
    ? 10 * CLOCK_FONT_GLYPH_BYTES + CLOCK_FONT_V2_COLON_WIDTH * CLOCK_FONT_GLYPH_HEIGHT / 8
    : CLOCK_FONT_GLYPHS.length * CLOCK_FONT_GLYPH_BYTES;
  const canvas = document.getElementById('clockFontCanvas');
  const width = CLOCK_FONT_GLYPHS.length * CLOCK_FONT_GLYPH_WIDTH;
  if (canvas.width === width && clockFontSourceCanvas) return;
  canvas.width = width;
  canvas.height = CLOCK_FONT_GLYPH_HEIGHT;
  initClockFontCanvas();
}

function initClockFontCanvas() {
  const canvas = document.getElementById('clockFontCanvas');
  clockFontSourceCanvas = document.createElement('canvas');
  clockFontSourceCanvas.width = canvas.width;
  clockFontSourceCanvas.height = canvas.height;
  const source = clockFontSourceCanvas.getContext('2d', { willReadFrequently: true });
  source.fillStyle = '#fff';
  source.fillRect(0, 0, canvas.width, canvas.height);
  source.fillStyle = '#000';
  source.textAlign = 'center';
  source.textBaseline = 'middle';
  source.font = 'bold 68px sans-serif';
  for (let index = 0; index < CLOCK_FONT_GLYPHS.length; index++)
    source.fillText(CLOCK_FONT_GLYPHS[index], index * CLOCK_FONT_GLYPH_WIDTH + CLOCK_FONT_GLYPH_WIDTH / 2,
      CLOCK_FONT_GLYPH_HEIGHT / 2 + 2);
  renderClockFontPreview();
}

function renderClockFontPreview() {
  if (!clockFontSourceCanvas) return;
  const canvas = document.getElementById('clockFontCanvas');
  const context = canvas.getContext('2d', { willReadFrequently: true });
  const source = clockFontSourceCanvas.getContext('2d', { willReadFrequently: true })
    .getImageData(0, 0, canvas.width, canvas.height);
  const threshold = parseInt(document.getElementById('clockFontThreshold').value, 10);
  for (let offset = 0; offset < source.data.length; offset += 4) {
    const luminance = source.data[offset] * 0.299 + source.data[offset + 1] * 0.587 + source.data[offset + 2] * 0.114;
    const value = luminance < threshold ? 0 : 255;
    source.data[offset] = source.data[offset + 1] = source.data[offset + 2] = value;
    source.data[offset + 3] = 255;
  }
  context.putImageData(source, 0, 0);
  document.getElementById('clockFontThresholdValue').textContent = threshold;
}

async function loadClockFontImage() {
  const file = document.getElementById('clockFontFile').files?.[0];
  if (!file || !clockFontSourceCanvas) return;
  const image = new Image();
  const url = URL.createObjectURL(file);
  try {
    await new Promise((resolve, reject) => {
      image.onload = resolve;
      image.onerror = reject;
      image.src = url;
    });
    const context = clockFontSourceCanvas.getContext('2d', { willReadFrequently: true });
    context.fillStyle = '#fff';
    context.fillRect(0, 0, clockFontSourceCanvas.width, clockFontSourceCanvas.height);
    context.drawImage(image, 0, 0, clockFontSourceCanvas.width, clockFontSourceCanvas.height);
    renderClockFontPreview();
    addLog(`时钟字库图片已加载：${file.name}`);
  } finally {
    URL.revokeObjectURL(url);
  }
}

function packClockFontImageData(imageData) {
  const packed = new Uint8Array(CLOCK_FONT_DATA_SIZE);
  for (let glyph = 0; glyph < CLOCK_FONT_GLYPHS.length; glyph++) {
    const glyphWidth = clockFontVersion >= 2 && glyph === 10 ? CLOCK_FONT_V2_COLON_WIDTH : CLOCK_FONT_GLYPH_WIDTH;
    const sourceX = glyph * CLOCK_FONT_GLYPH_WIDTH;
    const glyphOffset = glyph === 10 ? 10 * CLOCK_FONT_GLYPH_BYTES : glyph * CLOCK_FONT_GLYPH_BYTES;
    for (let y = 0; y < CLOCK_FONT_GLYPH_HEIGHT; y++) {
      for (let x = 0; x < glyphWidth; x++) {
        const sampleX = glyphWidth === CLOCK_FONT_GLYPH_WIDTH
          ? x : Math.floor((x + 0.5) * CLOCK_FONT_GLYPH_WIDTH / glyphWidth);
        const pixel = (y * imageData.width + sourceX + sampleX) * 4;
        if (imageData.data[pixel] < 128)
          packed[glyphOffset + y * (glyphWidth / 8) + (x >> 3)] |=
            0x80 >> (x & 7);
      }
    }
  }
  return packed;
}

function setClockFontStatus(message) {
  document.getElementById('clockFontStatus').textContent = message;
}

async function queryClockFont() {
  if (clockFontSupport && isBleConnected()) await write(EpdCmd.SET_FONT, new Uint8Array([4]));
}

async function uploadClockFont() {
  if (!clockFontSupport || clockFontBusy || !isBleConnected()) return;
  const canvas = document.getElementById('clockFontCanvas');
  const data = packClockFontImageData(canvas.getContext('2d').getImageData(0, 0, canvas.width, canvas.height));
  const chunkSize = Math.max(16, parseInt(document.getElementById('mtusize').value, 10) - 2);
  clockFontBusy = true;
  updateButtonStatus();
  setClockFontStatus('正在擦除字体区域...');
  try {
    const begin = new Uint8Array([clockFontVersion >= 2 ? 5 : 0]);
    if (!await write(EpdCmd.SET_FONT, begin)) return;
    for (let offset = 0; offset < data.length; offset += chunkSize) {
      const chunk = data.slice(offset, offset + chunkSize);
      if (!await write(EpdCmd.SET_FONT, new Uint8Array([1, ...chunk]))) return;
      setClockFontStatus(`正在上传字体：${Math.min(100, Math.round((offset + chunk.length) * 100 / data.length))}%`);
    }
    if (await write(EpdCmd.SET_FONT, new Uint8Array([2]))) {
      setClockFontStatus(`字体已上传（${CLOCK_FONT_GLYPH_WIDTH} × ${CLOCK_FONT_GLYPH_HEIGHT}），将在下次时钟刷新时使用。`);
      addLog('时钟字体上传完成。');
    }
  } finally {
    clockFontBusy = false;
    updateButtonStatus();
  }
}

async function eraseClockFont() {
  if (!clockFontSupport || clockFontBusy || !isBleConnected() || !confirm('确认恢复默认七段时钟字体？')) return;
  clockFontBusy = true;
  updateButtonStatus();
  try {
    if (await write(EpdCmd.SET_FONT, new Uint8Array([3]))) {
      setClockFontStatus('已恢复默认七段时钟字体。');
      addLog('自定义时钟字体已擦除。');
    }
  } finally {
    clockFontBusy = false;
    updateButtonStatus();
  }
}

function setOtaStatus(message, progress = null) {
  const status = document.getElementById('otaStatus');
  const progressBar = document.getElementById('otaProgress');
  if (status) status.textContent = message;
  if (progressBar && progress != null) progressBar.value = Math.max(0, Math.min(100, progress));
}

function toggleOtaPanel() {
  const panel = document.getElementById('ota-panel');
  const toggle = document.getElementById('otaPanelToggle');
  if (!panel || !toggle || otaBusy) return;
  const open = panel.hidden;
  panel.hidden = !open;
  toggle.setAttribute('aria-expanded', open ? 'true' : 'false');
}

function updateOtaControls() {
  const file = document.getElementById('otaFile');
  const enter = document.getElementById('otaEnterButton');
  const upload = document.getElementById('otaUploadButton');
  const cancel = document.getElementById('otaCancelButton');
  const toggle = document.getElementById('otaPanelToggle');
  if (!file || !enter || !upload || !cancel || !toggle) return;

  const connected = gattServer != null && gattServer.connected;
  const displayBusy = imageTransferActive || imageRefreshPending || slotActionPending || slotReadState !== null;
  file.disabled = otaBusy;
  enter.disabled = otaBusy || displayBusy || !otaPackage || !connected;
  upload.disabled = otaBusy || !otaPackage || connected;
  cancel.disabled = !otaBusy || otaClient == null;
  toggle.disabled = otaBusy;
}

async function updateOtaFileState() {
  const input = document.getElementById('otaFile');
  const file = input && input.files ? input.files[0] : null;
  otaPackage = null;
  otaPhase = 'idle';
  setOtaStatus(file ? '正在校验升级包...' : '请选择 EPD-nRF52-ota.zip。', 0);
  updateOtaControls();
  if (!file) return;

  try {
    otaPackage = await SecureDfu.parsePackage(file);
    setOtaStatus(`${file.name} · ${formatSlotBytes(otaPackage.firmware.length)} · CRC32 ${otaPackage.firmwareCrc.toString(16).padStart(8, '0').toUpperCase()}`, 0);
    addLog(`OTA 包校验通过：${otaPackage.firmware.length} 字节。`);
  } catch (error) {
    input.value = '';
    setOtaStatus(error.message || '升级包校验失败。', 0);
    addLog(error.message || '升级包校验失败。', '', 'error');
  }
  updateOtaControls();
}

async function enterOtaBootloader() {
  if (!otaPackage || otaBusy || !isBleConnected()) return;
  if (!confirm(`确认一键升级当前设备？\n升级包：${otaPackage.name}`)) return;

  let autoUpload = false;
  otaBusy = true;
  otaPhase = 'entering';
  setOtaStatus('正在切换到 DfuTarg...', 0);
  addLog('正在让设备进入原厂 Secure DFU 模式...');
  updateButtonStatus();
  try {
    await SecureDfu.enterBootloader(bleDevice);
    otaPhase = 'bootloader';
    setOtaStatus('DfuTarg 已启动，正在自动连接...', 0);
    addLog('设备已进入 DfuTarg，正在自动继续升级。');
    autoUpload = true;
  } catch (error) {
    otaPhase = 'idle';
    setOtaStatus(error.message || '进入升级模式失败。', 0);
    addLog(error.message || '进入升级模式失败。', '', 'error');
  } finally {
    otaBusy = false;
    updateButtonStatus();
  }
  if (autoUpload) await startOtaUpdate(true);
}

async function startOtaUpdate(grantedOnly = false) {
  if (!otaPackage || otaBusy || isBleConnected()) return;
  if (!grantedOnly && !confirm(`确认升级 ${otaPackage.name}？\n升级过程中请保持页面和蓝牙开启。`)) return;

  otaBusy = true;
  otaPhase = 'uploading';
  otaNextLogPercent = 10;
  setOtaStatus(grantedOnly ? '正在自动连接 DfuTarg...' : '请选择 DfuTarg 设备...', 0);
  addLog(grantedOnly ? '正在自动连接已授权的 DfuTarg...' : '正在搜索 DfuTarg...');
  otaClient = new SecureDfu.Client(otaPackage, {
    status: message => setOtaStatus(message),
    progress: (progress, message) => {
      const percent = Math.floor(progress);
      setOtaStatus(message, percent);
      if (percent >= otaNextLogPercent || percent === 100) {
        addLog(`OTA 传输进度：${percent}%`, '⇑');
        while (otaNextLogPercent <= percent) otaNextLogPercent += 10;
      }
    }
  });
  updateButtonStatus();

  try {
    await otaClient.upload({ grantedOnly });
    otaPhase = 'complete';
    setOtaStatus('升级完成，设备正在重启。', 100);
    addLog('OTA 校验和安装已完成，设备正在重启。');
  } catch (error) {
    const cancelled = otaClient && otaClient.cancelled;
    const permissionRequired = error && error.name === 'DfuPermissionRequired';
    otaPhase = permissionRequired ? 'bootloader' : (cancelled ? 'cancelled' : 'failed');
    const message = permissionRequired ? error.message : (cancelled ? 'OTA 已取消。' : (error.message || 'OTA 升级失败。'));
    setOtaStatus(message, 0);
    addLog(message, '', cancelled || permissionRequired ? '' : 'error');
  } finally {
    otaClient = null;
    otaBusy = false;
    updateButtonStatus();
  }
}

function cancelOtaUpdate() {
  if (!otaClient || !otaBusy) return;
  otaPhase = 'cancelling';
  setOtaStatus('正在取消 OTA...');
  otaClient.cancel();
  updateOtaControls();
}

function slotColorName(colorId) {
  return colorId === 2 ? '黑白' : colorId === 3 ? '黑白红' : colorId === 4 ? '黑白红黄' :
    colorId === 7 ? '七色' : '未知';
}

function rleEncode(data, maxLiteral = 128) {
  const input = data instanceof Uint8Array ? data : new Uint8Array(data);
  const output = [];
  let offset = 0;

  while (offset < input.length) {
    let runLength = 1;
    while (offset + runLength < input.length && runLength < 130 && input[offset + runLength] === input[offset]) {
      runLength++;
    }

    if (runLength >= 3) {
      output.push(0x80 | (runLength - 3), input[offset]);
      offset += runLength;
      continue;
    }

    const literalStart = offset;
    let literalLength = 0;
    while (offset < input.length && literalLength < maxLiteral &&
      !(offset + 2 < input.length && input[offset] === input[offset + 1] && input[offset] === input[offset + 2])) {
      offset++;
      literalLength++;
    }

    if (literalLength === 0) {
      literalLength = 1;
      offset++;
    }
    output.push(literalLength - 1);
    for (let index = literalStart; index < literalStart + literalLength; index++) output.push(input[index]);
  }

  return new Uint8Array(output);
}

function rleEncodeChunks(data, chunkSize) {
  const encoded = rleEncode(data, Math.min(chunkSize - 1, 128));
  const chunks = [];
  let tokenOffset = 0;
  let chunkOffset = 0;

  while (tokenOffset < encoded.length) {
    const token = encoded[tokenOffset];
    const tokenSize = (token & 0x80) !== 0 ? 2 : token + 2;
    if (tokenOffset - chunkOffset + tokenSize > chunkSize && tokenOffset > chunkOffset) {
      chunks.push(encoded.slice(chunkOffset, tokenOffset));
      chunkOffset = tokenOffset;
    }
    tokenOffset += tokenSize;
  }
  if (tokenOffset > chunkOffset) chunks.push(encoded.slice(chunkOffset, tokenOffset));
  return chunks;
}

function rleDecode(data) {
  const input = data instanceof Uint8Array ? data : new Uint8Array(data);
  const output = [];
  let offset = 0;

  while (offset < input.length) {
    const token = input[offset++];
    if ((token & 0x80) !== 0) {
      if (offset >= input.length) throw new Error('RLE repeat token is incomplete');
      const count = (token & 0x7F) + 3;
      const value = input[offset++];
      for (let index = 0; index < count; index++) output.push(value);
    } else {
      const count = token + 1;
      if (offset + count > input.length) throw new Error('RLE literal token is incomplete');
      for (let index = 0; index < count; index++) output.push(input[offset++]);
    }
  }

  return new Uint8Array(output);
}

function getSlotImageCacheScope() {
  const deviceId = bleDevice && (bleDevice.id || bleDevice.name) ? (bleDevice.id || bleDevice.name) : 'unknown-device';
  const driver = document.getElementById('epddriver');
  return `${deviceId}:${driver ? driver.value : 'unknown-driver'}`;
}

function getSlotImageCacheKey(slot) {
  return `${SLOT_IMAGE_CACHE_PREFIX}${encodeURIComponent(getSlotImageCacheScope())}:${slot}`;
}

function createSlotPreviewDataUrl(sourceImageData) {
  const source = document.createElement('canvas');
  source.width = sourceImageData.width;
  source.height = sourceImageData.height;
  source.getContext('2d').putImageData(sourceImageData, 0, 0);

  const scale = Math.min(1, SLOT_PREVIEW_MAX_EDGE / Math.max(source.width, source.height));
  const preview = document.createElement('canvas');
  preview.width = Math.max(1, Math.round(source.width * scale));
  preview.height = Math.max(1, Math.round(source.height * scale));
  const previewContext = preview.getContext('2d');
  previewContext.fillStyle = '#fff';
  previewContext.fillRect(0, 0, preview.width, preview.height);
  previewContext.drawImage(source, 0, 0, preview.width, preview.height);

  const dataUrl = preview.toDataURL('image/jpeg', SLOT_PREVIEW_JPEG_QUALITY);
  if (!dataUrl.startsWith('data:image/')) throw new Error('Canvas preview snapshot failed');
  return dataUrl;
}

function normalizeSlotFingerprint(value) {
  return typeof value === 'string' && /^[0-9a-f]{8}$/i.test(value) ? value.toUpperCase() : null;
}

function encodeUint32LE(value) {
  const bytes = new Uint8Array(4);
  new DataView(bytes.buffer).setUint32(0, value >>> 0, true);
  return bytes;
}

function encodeSlotAction(action, slot) {
  if (!slotProtocolV2) return new Uint8Array([action, slot & 0xFF]);
  const payload = new Uint8Array(5);
  payload[0] = action;
  payload.set(encodeUint32LE(slot), 1);
  return payload;
}

function encodeSlotIndex(slot) {
  return slotProtocolV2 ? encodeUint32LE(slot) : new Uint8Array([slot & 0xFF]);
}

function isSlotUsed(slot) {
  const offset = slot - slotState.pageStart;
  return offset >= 0 && offset < slotState.pageCount && (slotState.usedMask & (1 << offset)) !== 0;
}

function slotFingerprint(slot) {
  const offset = slot - slotState.pageStart;
  return offset >= 0 && offset < slotState.pageCount ? slotState.fingerprints[offset] || null : null;
}

function formatFlashSize(bytes) {
  if (!Number.isFinite(bytes) || bytes <= 0) return '未识别 Flash';
  if (bytes >= 1024 * 1024) return `${Number((bytes / (1024 * 1024)).toFixed(2))} MB Flash`;
  return `${Number((bytes / 1024).toFixed(1))} KB Flash`;
}

function slotCacheMatchesFingerprint(entry, fingerprint) {
  return fingerprint == null || normalizeSlotFingerprint(entry && entry.fingerprint) === fingerprint;
}

function loadSlotImageCache() {
  const scope = getSlotImageCacheScope();
  if (scope !== slotImageCacheScope) {
    slotImageCache = new Map();
    slotImageCacheScope = scope;
  }

  const pageEnd = slotState.pageStart + slotState.pageCount;
  for (let slot = slotState.pageStart; slot < pageEnd; slot++) {
    const used = isSlotUsed(slot);
    const pending = slotPreviewPending.has(slot);
    const fingerprint = slotFingerprint(slot);
    let staleCacheRemoved = false;
    if (!used && !pending) {
      removeSlotImageCache(slot);
      continue;
    }

    const currentEntry = slotImageCache.get(slot);
    if (used && !pending && currentEntry && !slotCacheMatchesFingerprint(currentEntry, fingerprint)) {
      slotImageCache.delete(slot);
      try { localStorage.removeItem(getSlotImageCacheKey(slot)); } catch (_) { }
      staleCacheRemoved = true;
    }

    try {
      const stored = localStorage.getItem(getSlotImageCacheKey(slot));
      if (stored) {
        const entry = JSON.parse(stored);
        if (entry && entry.dataUrl && entry.dataUrl.startsWith('data:image/')) {
          if (used && !pending && !slotCacheMatchesFingerprint(entry, fingerprint)) {
            localStorage.removeItem(getSlotImageCacheKey(slot));
            staleCacheRemoved = true;
          } else {
            const cachedEntry = slotImageCache.get(slot);
            const currentSavedAt = cachedEntry && Number(cachedEntry.savedAt) || 0;
            const storedSavedAt = Number(entry.savedAt) || 0;
            if (!cachedEntry || storedSavedAt > currentSavedAt) {
              slotImageCache.set(slot, entry);
            }
          }
        }
      }
    } catch (error) {
      console.warn('Failed to load slot image cache', error);
      try { localStorage.removeItem(getSlotImageCacheKey(slot)); } catch (_) { }
    }

    if (used && pending) {
      slotPreviewPending.delete(slot);
      const entry = slotImageCache.get(slot);
      if (entry && entry.pending) {
        saveSlotImageCache(slot, { ...entry, fingerprint, pending: false });
      }
    }
    if (staleCacheRemoved) addLog(`槽位 ${slot + 1} 已在其他浏览器或设备更新，旧预览已清除。`);
  }
}

function saveSlotImageCache(slot, entry) {
  slotImageCache.set(slot, entry);
  const cacheKey = getSlotImageCacheKey(slot);
  const serializedEntry = JSON.stringify(entry);
  try {
    localStorage.setItem(cacheKey, serializedEntry);
    return true;
  } catch (firstError) {
    try {
      localStorage.removeItem(cacheKey);
      localStorage.setItem(cacheKey, serializedEntry);
      return true;
    } catch (error) {
      console.warn('Failed to persist slot image cache', firstError, error);
      addLog('浏览器缓存空间不足，本次预览仅在当前页面有效。');
      return false;
    }
  }
}

function cacheCurrentSlotPreview(slot, processedData, mode) {
  try {
    const scope = getSlotImageCacheScope();
    if (scope !== slotImageCacheScope) {
      slotImageCache = new Map();
      slotImageCacheScope = scope;
    }
    const sourceImageData = ditherSourceImageData &&
      ditherSourceImageData.width === canvas.width && ditherSourceImageData.height === canvas.height
      ? ditherSourceImageData
      : ctx.getImageData(0, 0, canvas.width, canvas.height);
    const dataUrl = createSlotPreviewDataUrl(sourceImageData);
    const colorId = mode === 'sevenColor' ? 7 : mode === 'blackWhiteColor' ? 2 : mode === 'threeColor' ? 3 : 4;
    slotPreviewPending.add(slot);
    saveSlotImageCache(slot, {
      width: canvas.width,
      height: canvas.height,
      size: processedData.length,
      colorId,
      dataUrl,
      previewKind: 'original',
      fingerprint: null,
      pending: true,
      savedAt: new Date().getTime()
    });
    renderSlotGrid(true);
    addLog(`槽位 ${slot + 1} 原图预览已生成，无需再次回读。`);
  } catch (error) {
    console.warn('Failed to cache current slot preview', error);
    removeSlotImageCache(slot);
    addLog(`槽位 ${slot + 1} 预览生成失败：${error.message || error}`);
  }
}

function removeSlotImageCache(slot) {
  slotPreviewPending.delete(slot);
  slotImageCache.delete(slot);
  try { localStorage.removeItem(getSlotImageCacheKey(slot)); } catch (_) { }
}

function clearAllSlotImageCaches() {
  for (const slot of slotImageCache.keys()) removeSlotImageCache(slot);
  slotImageCache.clear();
}

function renderSlotGrid(forceDisabled = imageTransferActive || slotActionPending || slotReadState !== null) {
  const grid = document.getElementById('slotGrid');
  const summary = document.getElementById('slotSummary');
  const hint = document.getElementById('slotHint');
  const pagination = document.getElementById('slotPagination');
  if (!grid || !summary || !hint || !pagination) return;

  grid.replaceChildren();
  grid.hidden = true;
  pagination.hidden = true;
  if (!isBleConnected()) {
    summary.textContent = '连接设备后读取槽位';
    hint.textContent = '图片保存在设备外置 Flash 中';
    return;
  }

  if (slotState.count === 0) {
    summary.textContent = '未识别到外置 Flash';
    hint.textContent = '请检查 Flash 供电及 P0.12 至 P0.15 连线';
    return;
  }

  grid.hidden = false;
  let usedCount = 0;
  const pageEnd = slotState.pageStart + slotState.pageCount;
  for (let slot = slotState.pageStart; slot < pageEnd; slot++) {
    const used = isSlotUsed(slot);
    const cached = slotImageCache.get(slot) || null;
    const previewPending = !used && cached && slotPreviewPending.has(slot);
    if (used) usedCount++;

    const item = document.createElement('div');
    item.className = used ? 'slot-item used' : 'slot-item';
    if (slotState.selected === slot) item.classList.add('selected');

    const label = document.createElement('div');
    label.className = 'slot-label';
    const title = document.createElement('strong');
    title.textContent = `槽位 ${slot + 1}`;
    const state = document.createElement('span');
    state.className = 'slot-state';
    state.textContent = `${used ? '已存图片' : previewPending ? '正在存入' : '空闲'}${cached ? ' · 已缓存' : used ? ' · 未读取' : ''}${slotState.selected === slot ? ' · 当前' : ''}`;
    label.append(title, state);

    const actions = document.createElement('div');
    actions.className = 'slot-actions';

    const saveButton = document.createElement('button');
    saveButton.type = 'button';
    saveButton.className = 'primary';
    saveButton.textContent = used ? '覆盖' : '存入';
    saveButton.disabled = forceDisabled;
    saveButton.addEventListener('click', () => saveImageToSlot(slot));

    const displayButton = document.createElement('button');
    displayButton.type = 'button';
    displayButton.className = 'secondary';
    displayButton.textContent = '显示';
    displayButton.disabled = forceDisabled || !used;
    displayButton.addEventListener('click', () => displayImageSlot(slot));

    const readControl = document.createElement('div');
    readControl.className = cached ? 'slot-read-control cached' : 'slot-read-control';
    readControl.hidden = !slotStreamSupport;
    const readButton = document.createElement('button');
    readButton.type = 'button';
    readButton.className = 'secondary';
    readButton.textContent = '读取';
    readButton.disabled = forceDisabled || !used;
    readButton.addEventListener('click', () => readImageSlot(slot));

    const hoverPreview = document.createElement('div');
    hoverPreview.className = cached ? 'slot-hover-preview cached' : 'slot-hover-preview empty';
    hoverPreview.id = `slotPreviewTooltip${slot}`;
    hoverPreview.setAttribute('role', 'tooltip');
    readButton.setAttribute('aria-describedby', hoverPreview.id);
    readButton.title = cached ? '悬停预览已缓存图片' : '点击读取图片并生成网页缓存';
    if (cached) {
      const previewImage = document.createElement('img');
      previewImage.src = cached.dataUrl;
      previewImage.alt = `槽位 ${slot + 1} 缓存预览`;
      const previewMeta = document.createElement('span');
      const previewKind = cached.previewKind === 'original' ? '原图' : '设备回读';
      previewMeta.textContent = `${cached.width} × ${cached.height} · ${slotColorName(cached.colorId)} · ${previewKind}`;
      hoverPreview.append(previewImage, previewMeta);
    } else {
      hoverPreview.textContent = used ? '尚未读取，点击“读取”后可悬停预览' : '空槽位，无图片可读取';
    }
    readControl.append(readButton, hoverPreview);

    const freeButton = document.createElement('button');
    freeButton.type = 'button';
    freeButton.className = 'secondary slot-delete';
    freeButton.textContent = '删除';
    freeButton.disabled = forceDisabled || !used;
    freeButton.addEventListener('click', () => freeImageSlot(slot));

    actions.append(saveButton, displayButton, readControl, freeButton);
    item.append(label, actions);
    grid.appendChild(item);
  }

  const page = slotProtocolV2 ? Math.floor(slotState.pageStart / SLOT_PAGE_SIZE) + 1 : 1;
  const pages = slotProtocolV2 ? Math.ceil(slotState.count / SLOT_PAGE_SIZE) : 1;
  summary.textContent = `${formatFlashSize(slotState.flashSize)} · ${slotState.count} 个槽位`;
  hint.textContent = `${pages > 1 ? `第 ${page}/${pages} 页 · ` : ''}本页已使用 ${usedCount} 个 · “存入”仅保存到设备，不刷新屏幕`;
  pagination.hidden = pages <= 1;
  document.getElementById('slotPageStatus').textContent = `${page} / ${pages}`;
  document.getElementById('slotPrevPage').disabled = forceDisabled || slotState.pageStart === 0;
  document.getElementById('slotNextPage').disabled = forceDisabled || pageEnd >= slotState.count;
}

async function refreshSlots(start = slotState.pageStart) {
  if (!isBleConnected()) return;
  addLog('正在读取图片槽位...');
  const normalizedStart = Math.max(0, start);
  if (nrfEpdCharacteristic) {
    const response = waitForNativeNrfMessage(message => {
      const match = /^slots=\d+\s+(\d+)\s+/.exec(message.trim());
      return match && parseInt(match[1], 10) === normalizedStart;
    }, 8000, '图片槽位状态');
    await writeNativeNrfPayload(new Uint8Array([
      EpdCmd.GET_SLOTS,
      ...encodeUint32LE(normalizedStart),
    ]), false);
    return response;
  }
  await write(EpdCmd.GET_SLOTS, encodeUint32LE(normalizedStart));
}

async function findFirstFreeNativeSlot() {
  if (!nrfEpdCharacteristic || slotState.count === 0) return null;
  const total = slotState.count;
  for (let start = 0; start < total; start += SLOT_PAGE_SIZE) {
    await refreshSlots(start);
    for (let offset = 0; offset < slotState.pageCount; offset++) {
      if ((slotState.usedMask & (1 << offset)) === 0)
        return slotState.pageStart + offset;
    }
  }
  return null;
}

async function changeSlotPage(direction) {
  const start = Math.max(0, Math.min(slotState.count - 1, slotState.pageStart + direction * SLOT_PAGE_SIZE));
  await refreshSlots(start);
}

function applySlotsMessage(message) {
  const parts = message.trim().split(/\s+/);
  const countMatch = /^slots=(\d+)$/.exec(parts[0] || '');
  if (!countMatch || parts.length < 2 || !/^(?:0x[0-9a-f]+|\d+)$/i.test(parts[1])) return false;

  const count = parseInt(countMatch[1], 10);
  const dynamicFormat = parts.length >= 6 && parts.slice(1, 6).every((part) => /^\d+$/.test(part));
  if (dynamicFormat) {
    slotProtocolV2 = true;
    const pageStart = parseInt(parts[1], 10);
    const pageCount = parseInt(parts[2], 10);
    const usedMask = Number(parts[3]);
    const selected = parseInt(parts[4], 10);
    const flashSize = parseInt(parts[5], 10);
    slotState = {
      count,
      pageStart,
      pageCount,
      usedMask,
      selected,
      flashSize,
      fingerprints: parts.slice(6, 6 + pageCount).map(normalizeSlotFingerprint)
    };
    tgzStorageAvailable = count > 0;
  } else {
  slotProtocolV2 = false;
  let fingerprintStart = 2;
  let selected = null;
  if (parts[2] != null && /^\d+$/.test(parts[2])) {
    selected = parseInt(parts[2], 10);
    fingerprintStart = 3;
  }
  const fingerprints = parts.slice(fingerprintStart, fingerprintStart + count)
    .map(normalizeSlotFingerprint);
  slotState = {
    count,
    pageStart: 0,
    pageCount: count,
    usedMask: Number(parts[1]),
    selected,
    flashSize: 0,
    fingerprints
  };
  }
  loadSlotImageCache();
  renderSlotGrid();
  const eraseAllCompleted = slotEraseAllPending && slotState.usedMask === 0;
  if (slotEraseAllPending && !eraseAllCompleted) {
    updateButtonStatus();
    return true;
  }
  slotEraseAllPending = false;
  if (slotActionPending) setSlotActionPending(false);
  else updateButtonStatus();
  if (eraseAllCompleted) {
    clearAllSlotImageCaches();
    const status = document.getElementById('slotReadStatus');
    status.hidden = false;
    status.textContent = '全部图片槽位已擦除。';
    addLog('全部图片槽位擦除完成。');
  }
  return true;
}

async function saveImageToSlot(slot) {
  if (imageTransferActive || slotActionPending) return;
  const imageFile = document.getElementById('imageFile');
  if (!imageFile || imageFile.files.length === 0) {
    alert('请先选择图片，再存入图片槽。');
    addLog(`槽位 ${slot + 1} 未存入：尚未选择图片。`);
    return;
  }
  const used = isSlotUsed(slot);
  if (used && !confirm(`槽位 ${slot + 1} 已有图片，确认覆盖？`)) return;
  const refreshAfterSave = document.getElementById('slotRefreshAfterSave').checked;
  await sendimg({ slot, refreshAfterSave });
}

async function freeImageSlot(slot) {
  if (imageTransferActive || slotActionPending) return;
  if (!confirm(`确认删除槽位 ${slot + 1} 的图片？`)) return;
  setSlotActionPending(true);
  const sent = nrfEpdCharacteristic
    ? await writeNativeNrfPayload(new Uint8Array([
        EpdCmd.FREE_SLOT,
        ...encodeUint32LE(slot),
      ]), false).then(() => true, () => false)
    : await write(EpdCmd.FREE_SLOT, encodeSlotIndex(slot));
  if (sent) {
    removeSlotImageCache(slot);
    renderSlotGrid(true);
    addLog(`槽位 ${slot + 1} 删除命令已发送。`);
  } else {
    setSlotActionPending(false);
  }
}

async function freeAllImageSlots() {
  if (imageTransferActive || slotActionPending || slotReadState || slotState.count === 0) return;
  if (!confirm('确认擦除全部图片槽位？所有已保存图片都将永久删除，此操作不可恢复。')) return;

  slotEraseAllPending = true;
  setSlotActionPending(true);
  const status = document.getElementById('slotReadStatus');
  status.hidden = false;
  status.textContent = '正在擦除全部图片槽位，请勿断开连接...';
  const sent = nrfEpdCharacteristic
    ? await writeNativeNrfPayload(new Uint8Array([
        EpdCmd.FREE_SLOT,
        ...encodeUint32LE(0xFFFFFFFF),
      ]), false).then(() => true, () => false)
    : await write(EpdCmd.FREE_SLOT, encodeSlotIndex(0xFFFFFFFF));
  if (sent) {
    addLog('全部图片槽位擦除命令已发送。');
  } else {
    slotEraseAllPending = false;
    setSlotActionPending(false);
    status.textContent = '全部槽位擦除命令发送失败。';
  }
}

async function displayImageSlot(slot) {
  if (imageTransferActive || slotActionPending) return;
  setSlotActionPending(true);
  const sent = nrfEpdCharacteristic
    ? await writeNativeNrfPayload(new Uint8Array([
        EpdCmd.SET_SLOT,
        ...encodeNativeSlotAction(1, slot),
      ]), false).then(() => true, () => false)
    : await write(EpdCmd.SET_SLOT, encodeSlotAction(1, slot));
  if (sent) {
    addLog(`已请求设备显示槽位 ${slot + 1}。`);
  } else {
    setSlotActionPending(false);
  }
}

function setSlotActionPending(pending) {
  slotActionPending = pending;
  if (slotActionTimer != null) clearTimeout(slotActionTimer);
  slotActionTimer = null;
  if (pending) {
    slotActionTimer = setTimeout(() => {
      slotActionPending = false;
      slotEraseAllPending = false;
      slotActionTimer = null;
      updateButtonStatus();
      addLog('槽位操作等待超时，控制按钮已恢复。');
    }, 95000);
  }
  updateButtonStatus();
}

function cancelImageRefreshWait() {
  if (imageRefreshTimer != null) clearTimeout(imageRefreshTimer);
  imageRefreshTimer = null;
  imageRefreshPending = false;
}

function cancelImagePrepareWait() {
  if (imagePrepareWait == null) return false;
  clearTimeout(imagePrepareWait.timer);
  const resolve = imagePrepareWait.resolve;
  imagePrepareWait = null;
  resolve(false);
  return true;
}

function startImagePrepareWait() {
  cancelImagePrepareWait();
  return new Promise(resolve => {
    const wait = { resolve, timer: null };
    wait.timer = setTimeout(() => {
      if (imagePrepareWait !== wait) return;
      imagePrepareWait = null;
      addLog('5.65寸屏幕初始化完成通知超时。', '', 'error');
      resolve(false);
    }, IMAGE_REFRESH_TIMEOUT_MS);
    imagePrepareWait = wait;
  });
}

function completeImagePrepare() {
  if (imagePrepareWait == null) return false;
  clearTimeout(imagePrepareWait.timer);
  const resolve = imagePrepareWait.resolve;
  imagePrepareWait = null;
  resolve(true);
  addLog('5.65寸屏幕初始化完成，继续传输。');
  return true;
}

function startImageRefreshWait(kind = 'refresh') {
  cancelImageRefreshWait();
  imageCompletionKind = kind;
  imageRefreshPending = true;
  imageRefreshTimer = setTimeout(() => {
    if (!imageRefreshPending) return;
    imageRefreshPending = false;
    imageRefreshTimer = null;
    imageTransferActive = false;
    updateButtonStatus();
    const action = imageCompletionKind === 'slot' ? '槽位保存' : '屏幕刷新';
    setStatus(`${action}完成通知超时。`);
    addLog(`${action}完成通知超时，控制按钮已恢复。`);
  }, IMAGE_REFRESH_TIMEOUT_MS);
}

function completeImageRefresh() {
  if (!imageRefreshPending) return false;

  const completionKind = imageCompletionKind;
  cancelImageRefreshWait();
  imageTransferActive = false;
  updateButtonStatus();
  const totalTime = (new Date().getTime() - startTime) / 1000.0;
  const action = completionKind === 'slot' ? '槽位保存' : '屏幕刷新';
  setStatus(`${action}完成！总耗时: ${totalTime}s`);
  addLog(`${action}完成，可以继续操作。总耗时: ${totalTime}s`);
  imageCompletionKind = 'refresh';
  if (completionKind === 'slot') void refreshSlots();
  const status = document.getElementById('status');
  setTimeout(() => {
    status.parentElement.style.display = 'none';
  }, 5000);
  return true;
}

async function startSlotSlide(randomMode = false) {
  if (slotState.count === 0) {
    alert('请先存入至少一张图片，再启动轮播。');
    addLog('轮播未启动：没有可用的图片槽。');
    return false;
  }
  const input = document.getElementById('slotSlideMinutes');
  const minutes = Math.max(1, Math.min(65535, parseInt(input.value, 10) || 1));
  input.value = minutes;
  setSlotActionPending(true);
  if (await write(EpdCmd.SET_SLIDE, new Uint8Array([minutes >> 8, minutes & 0xFF, randomMode ? 1 : 0]))) {
    addLog(`${randomMode ? '随机' : '顺序'}轮播已启动，正在立即显示${randomMode ? '随机图片' : '第一张图片'}，间隔 ${minutes} 分钟。`);
    return true;
  }
  setSlotActionPending(false);
  return false;
}

async function startRandomSlotSlide() {
  return startSlotSlide(true);
}

async function stopSlotSlide() {
  if (await write(EpdCmd.SET_SLIDE, new Uint8Array([0, 0]))) {
    addLog('图片轮播已停止。');
  }
}

async function readImageSlot(slot) {
  if (slotImageCache.has(slot)) {
    addLog(`槽位 ${slot + 1} 已有网页缓存，悬停“读取”按钮即可预览。`);
    return;
  }
  if (slotReadState) {
    addLog('已有槽位图片正在读取，请稍候。');
    return;
  }
  if (imageTransferActive || slotActionPending) return;

  const status = document.getElementById('slotReadStatus');
  status.hidden = false;
  status.textContent = `正在读取槽位 ${slot + 1}...`;
  slotReadState = { slot, pending: true, infoAttempts: 0, startedAt: new Date().getTime() };
  updateButtonStatus();
  await requestSlotImageInfo(slotReadState);
}

async function requestSlotImageInfo(state) {
  if (!state || slotReadState !== state || !state.pending) return;

  state.infoAttempts++;
  clearSlotReadTimer();
  slotReadTimer = setTimeout(() => {
    if (slotReadState !== state || !state.pending) return;
    if (state.infoAttempts < 2) {
      addLog('设备未返回图片信息，正在重试。');
      void requestSlotImageInfo(state);
    } else {
      failSlotImageRead('设备未返回图片信息，读取超时。');
    }
  }, SLOT_READ_INFO_TIMEOUT_MS);

  if (!await write(EpdCmd.GET_IMAGE, encodeSlotIndex(state.slot), false) && slotReadState === state) {
    if (state.infoAttempts < 2) {
      addLog('读取命令发送失败，正在重试。');
      void requestSlotImageInfo(state);
    } else {
      failSlotImageRead('读取命令发送失败。');
    }
  }
}

function clearSlotReadTimer() {
  if (slotReadTimer != null) clearTimeout(slotReadTimer);
  slotReadTimer = null;
}

function failSlotImageRead(message) {
  clearSlotReadTimer();
  slotReadState = null;
  const status = document.getElementById('slotReadStatus');
  status.hidden = false;
  status.textContent = message;
  addLog(message);
  updateButtonStatus();
}

function retrySlotChunk(index, reason) {
  const state = slotReadState;
  if (!state || state.pending || state.nextChunkIndex !== index) return;

  clearSlotReadTimer();
  state.expectedChunk = null;
  if (state.chunkRetries >= SLOT_CHUNK_MAX_RETRIES) {
    failSlotImageRead(`第 ${index + 1} 个数据块${reason}，重试 ${SLOT_CHUNK_MAX_RETRIES} 次后读取已停止。`);
    return;
  }

  state.chunkRetries++;
  addLog(`第 ${index + 1} 个数据块${reason}，正在重试 (${state.chunkRetries}/${SLOT_CHUNK_MAX_RETRIES})。`);
  void requestSlotChunk(index, true);
}

function armSlotChunkTimeout(index) {
  clearSlotReadTimer();
  const state = slotReadState;
  slotReadTimer = setTimeout(() => {
    if (slotReadState !== state) return;
    if (state.streaming) {
      failSlotImageRead(`连续读取第 ${index + 1} 个数据块超时，请重试。`);
    } else {
      retrySlotChunk(index, '接收超时');
    }
  }, SLOT_READ_TIMEOUT_MS);
}

async function startSlotImageStream() {
  const state = slotReadState;
  if (!state || state.pending) return;

  state.streaming = true;
  state.nextChunkIndex = 0;
  state.expectedChunk = null;
  armSlotChunkTimeout(0);
  const request = new Uint8Array(slotProtocolV2 ? 5 : 2);
  request.set(encodeSlotIndex(state.slot));
  request[request.length - 1] = 1;
  if (!await write(EpdCmd.GET_IMAGE, request, false) && slotReadState === state) {
    failSlotImageRead('连续读取命令发送失败。');
  }
}

async function requestSlotChunk(index, retry = false) {
  const state = slotReadState;
  if (!state || state.pending) return;

  if (!retry) state.chunkRetries = 0;
  state.nextChunkIndex = index;
  state.expectedChunk = null;
  armSlotChunkTimeout(index);
  const request = new Uint8Array(slotProtocolV2 ? 6 : 3);
  request.set(encodeSlotIndex(state.slot));
  request[request.length - 2] = (index >> 8) & 0xFF;
  request[request.length - 1] = index & 0xFF;
  if (!await write(EpdCmd.GET_IMAGE, request, false) && slotReadState === state &&
    state.nextChunkIndex === index) {
    retrySlotChunk(index, '请求失败');
  }
}

function beginSlotImageRead(message) {
  const match = /^img=(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)(?:\s+(\d+))?$/.exec(message.trim());
  if (!match) return false;

  const slot = parseInt(match[1], 10);
  if (slotReadState && !slotReadState.pending && slotReadState.slot === slot) return true;

  const size = parseInt(match[4], 10);
  if (!Number.isFinite(size) || size <= 0 || size > MAX_SLOT_IMAGE_SIZE) {
    failSlotImageRead(`槽位图片大小异常：${size} 字节`);
    return true;
  }

  const startedAt = slotReadState && slotReadState.startedAt
    ? slotReadState.startedAt
    : new Date().getTime();
  clearSlotReadTimer();
  slotReadState = {
    slot,
    width: parseInt(match[2], 10),
    height: parseInt(match[3], 10),
    size,
    colorId: parseInt(match[5], 10),
    data: new Uint8Array(size),
    received: 0,
    expectedChunk: null,
    nextChunkIndex: 0,
    chunkRetries: 0,
    nextLogPercent: 10,
    rawChunkSize: match[6] == null ? DEFAULT_SLOT_READ_RAW_CHUNK_SIZE : parseInt(match[6], 10),
    streaming: false,
    startedAt,
    pending: false
  };

  if (!Number.isFinite(slotReadState.rawChunkSize) || slotReadState.rawChunkSize <= 0 ||
    slotReadState.rawChunkSize > 4096) {
    failSlotImageRead(`槽位数据块大小异常：${slotReadState.rawChunkSize}`);
    return true;
  }

  const status = document.getElementById('slotReadStatus');
  status.hidden = false;
  status.textContent = `槽位 ${slotReadState.slot + 1}：准备接收 ${formatSlotBytes(size)}`;
  if (slotStreamSupport)
    void startSlotImageStream();
  else
    void requestSlotChunk(0);
  return true;
}

function beginSlotChunk(message) {
  if (!slotReadState) return false;
  const match = /^chunk=(\d+)\s+len=(\d+)(?:\s+rle=(\d+))?$/.exec(message.trim());
  if (!match) return false;

  const index = parseInt(match[1], 10);
  if (index !== slotReadState.nextChunkIndex) {
    failSlotImageRead(`数据块序号异常：应为 ${slotReadState.nextChunkIndex + 1}，实际为 ${index + 1}。`);
    return true;
  }

  slotReadState.expectedChunk = {
    index,
    length: parseInt(match[2], 10),
    compressed: match[3] === '1',
    received: 0,
    parts: []
  };
  armSlotChunkTimeout(index);
  return true;
}

function receiveSlotChunk(data) {
  if (!slotReadState || !slotReadState.expectedChunk) return false;

  const expected = slotReadState.expectedChunk;
  if (expected.received + data.length > expected.length) {
    failSlotImageRead(`第 ${expected.index + 1} 个数据块长度异常，读取已停止。`);
    return true;
  }

  expected.parts.push(data.slice());
  expected.received += data.length;
  if (expected.received < expected.length) {
    armSlotChunkTimeout(expected.index);
    return true;
  }

  const chunkData = new Uint8Array(expected.length);
  let chunkOffset = 0;
  for (const part of expected.parts) {
    chunkData.set(part, chunkOffset);
    chunkOffset += part.length;
  }
  slotReadState.expectedChunk = null;

  let decoded;
  try {
    decoded = expected.compressed ? rleDecode(chunkData) : chunkData;
  } catch (error) {
    console.error(error);
    failSlotImageRead(`第 ${expected.index + 1} 个 RLE 数据块解析失败。`);
    return true;
  }

  const remaining = slotReadState.size - slotReadState.received;
  const expectedRawLength = Math.min(slotReadState.rawChunkSize, remaining);
  if (decoded.length !== expectedRawLength) {
    failSlotImageRead(`第 ${expected.index + 1} 个数据块解压长度异常。`);
    return true;
  }

  slotReadState.data.set(decoded, slotReadState.received);
  slotReadState.received += decoded.length;
  const percent = Math.round(slotReadState.received * 100 / slotReadState.size);
  const status = document.getElementById('slotReadStatus');
  status.hidden = false;
  status.textContent = `正在读取槽位 ${slotReadState.slot + 1}：${percent}% (${formatSlotBytes(slotReadState.received)} / ${formatSlotBytes(slotReadState.size)})`;

  if (percent >= slotReadState.nextLogPercent || slotReadState.received === slotReadState.size) {
    addLog(`槽位 ${slotReadState.slot + 1} 读取进度：${percent}%`, '⇓');
    while (slotReadState.nextLogPercent <= percent) slotReadState.nextLogPercent += 10;
  }

  if (slotReadState.received === slotReadState.size) {
    finishSlotImageRead();
  } else if (slotReadState.streaming) {
    slotReadState.nextChunkIndex = expected.index + 1;
    armSlotChunkTimeout(expected.index + 1);
  } else {
    void requestSlotChunk(expected.index + 1);
  }
  return true;
}

function restoreRotated1bpp(data, width, height) {
  const output = new Uint8Array(Math.ceil(width * height / 8)).fill(0xFF);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      set1bppPixel(output, width, x, y, get1bppPixel(data, height, y, width - 1 - x));
    }
  }
  return output;
}

function restoreRotated2bpp(data, width, height) {
  const output = new Uint8Array(Math.ceil(width * height / 4));
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      set2bppPixel(output, width, x, y, get2bppPixel(data, height, height - 1 - y, x));
    }
  }
  return output;
}

function restoreSSD1619_213_250x122Plane(data) {
  const nativeWidth = 128;
  const activeWidth = 250;
  const activeHeight = 122;
  const output = new Uint8Array(Math.ceil(activeWidth / 8) * activeHeight).fill(0xFF);
  for (let y = 0; y < activeHeight; y++) {
    for (let x = 0; x < activeWidth; x++) {
      set1bppPixel(output, activeWidth, x, y,
        get1bppPixel(data, nativeWidth, y, activeWidth - 1 - x));
    }
  }
  return output;
}

function normalizeSlotImageData(meta) {
  const driverSelect = document.getElementById('epddriver');
  const needsNativeRotation = meta.width === 416 && meta.height === 240 &&
    (isGDEM037F51Driver(driverSelect) || isGDEY037Z03Driver(driverSelect));
  if (!needsNativeRotation) return meta.data;

  if (meta.colorId === 4) return restoreRotated2bpp(meta.data, meta.width, meta.height);
  if (meta.colorId === 2) return restoreRotated1bpp(meta.data, meta.width, meta.height);
  if (meta.colorId === 3) {
    const planeSize = Math.floor(meta.data.length / 2);
    const output = new Uint8Array(meta.data.length);
    output.set(restoreRotated1bpp(meta.data.slice(0, planeSize), meta.width, meta.height), 0);
    output.set(restoreRotated1bpp(meta.data.slice(planeSize), meta.width, meta.height), planeSize);
    return output;
  }
  return meta.data;
}

function decodeUC8159SlotData(data, width, height) {
  const imageData = new ImageData(width, height);
  for (let pixel = 0; pixel < width * height; pixel++) {
    const packed = data[pixel >> 1];
    const value = (pixel & 1) === 0 ? (packed >> 4) & 0x0F : packed & 0x0F;
    const index = pixel * 4;
    if (value === 0x04) {
      imageData.data[index] = 255;
      imageData.data[index + 1] = 0;
      imageData.data[index + 2] = 0;
    } else {
      const channel = value === 0x00 ? 0 : 255;
      imageData.data[index] = channel;
      imageData.data[index + 1] = channel;
      imageData.data[index + 2] = channel;
    }
    imageData.data[index + 3] = 255;
  }
  return imageData;
}

function finishSlotImageRead() {
  const meta = slotReadState;
  const elapsed = (new Date().getTime() - meta.startedAt) / 1000.0;
  clearSlotReadTimer();
  slotReadState = null;
  try {
    const mode = meta.colorId === 2 ? 'blackWhiteColor' : meta.colorId === 3 ? 'threeColor' :
      meta.colorId === 4 ? 'fourColor' : meta.colorId === 6 ? 'sixColor' : 'sevenColor';
    let normalized = normalizeSlotImageData(meta);
    const driverValue = document.getElementById('epddriver').value.toLowerCase();
    let previewWidth = meta.width;
    let previewHeight = meta.height;
    if (driverValue === '19' && meta.width === 128 && meta.height === 250 && meta.colorId === 3) {
      const planeSize = Math.ceil(meta.width / 8) * meta.height;
      const black = restoreSSD1619_213_250x122Plane(normalized.slice(0, planeSize));
      const red = restoreSSD1619_213_250x122Plane(normalized.slice(planeSize, planeSize * 2));
      normalized = new Uint8Array(black.length + red.length);
      normalized.set(black, 0);
      normalized.set(red, black.length);
      previewWidth = 250;
      previewHeight = 122;
    }
    const imageData = (driverValue === '08' || driverValue === '09')
      ? decodeUC8159SlotData(normalized, previewWidth, previewHeight)
      : decodeProcessedData(normalized, previewWidth, previewHeight, mode);
    const existingPreview = slotImageCache.get(meta.slot);
    if (!existingPreview || existingPreview.previewKind !== 'original') {
      saveSlotImageCache(meta.slot, {
        width: previewWidth,
        height: previewHeight,
        size: meta.size,
        colorId: meta.colorId,
        dataUrl: createSlotPreviewDataUrl(imageData),
        previewKind: 'device',
        fingerprint: slotFingerprint(meta.slot),
        savedAt: new Date().getTime()
      });
    }
    renderSlotGrid();

    const status = document.getElementById('slotReadStatus');
    status.hidden = false;
    status.textContent = `槽位 ${meta.slot + 1} 读取完成，悬停“读取”按钮即可预览。耗时 ${elapsed}s。`;
    addLog(`槽位 ${meta.slot + 1} 图片已缓存，耗时: ${elapsed}s。`);
  } catch (error) {
    console.error(error);
    const status = document.getElementById('slotReadStatus');
    status.hidden = false;
    status.textContent = '图片数据解析失败。';
  } finally {
    updateButtonStatus();
  }
}

async function writeImage(data, step = 'bw', waitForPrepare = false) {
  const chunkSize = parseInt(document.getElementById('mtusize').value, 10) - 2;
  const interleavedCount = parseInt(document.getElementById('interleavedcount').value, 10);

  if (chunkSize <= 0) {
    addLog('MTU error, please reconnect the device.');
    return false;
  }

  const rawData = data instanceof Uint8Array ? data : new Uint8Array(data);
  const rleChunks = rleSupport && chunkSize >= 2 ? rleEncodeChunks(rawData, chunkSize) : [];
  const compressedSize = rleChunks.reduce((total, chunk) => total + chunk.length, 0);
  const useRle = rleSupport && compressedSize > 0 && compressedSize < rawData.length;
  const count = useRle ? rleChunks.length : Math.ceil(rawData.length / chunkSize);
  const stepName = step === 'bw' ? '图像' : '颜色';
  const transferSize = useRle ? compressedSize : rawData.length;
  let noReplyCount = interleavedCount;
  let nextLogPercent = 10;
  let preparePromise = null;

  if (useRle) addLog(`${stepName} RLE 压缩：${rawData.length} → ${compressedSize} 字节 (${(compressedSize * 100 / rawData.length).toFixed(1)}%)`);
  addLog(`${stepName}开始传输：${transferSize} 字节，共 ${count} 包。`, '⇑');

  for (let chunkIdx = 0; chunkIdx < count; chunkIdx++) {
    if (displayErrorActive) return false;
    if (chunkIdx === 0 && waitForPrepare) {
      preparePromise = startImagePrepareWait();
      setStatus('5.65寸屏幕正在初始化...');
      addLog('5.65寸屏幕开始初始化，完成后自动继续传输。');
    }
    const offset = chunkIdx * chunkSize;
    const chunk = useRle ? rleChunks[chunkIdx] : rawData.slice(offset, offset + chunkSize);
    const currentTime = (new Date().getTime() - startTime) / 1000.0;
    setStatus(`${stepName}块: ${chunkIdx + 1}/${count}, 总用时: ${currentTime}s`);

    const cfg = rleSupport
      ? (step === 'bw' ? 0 : 1) | (chunkIdx === 0 ? 2 : 0) | (useRle ? 4 : 0)
      : (step === 'bw' ? 0x0F : 0x00) | (chunkIdx === 0 ? 0x00 : 0xF0);
    const payload = [
      cfg,
      ...chunk,
    ];
    if (noReplyCount > 0) {
      if (!await write(EpdCmd.WRITE_IMG, payload, false)) return false;
      noReplyCount--;
    } else {
      if (!await write(EpdCmd.WRITE_IMG, payload, true)) return false;
      noReplyCount = interleavedCount;
    }

    if (chunkIdx === 0 && preparePromise && !await preparePromise) return false;

    const percent = Math.floor((chunkIdx + 1) * 100 / count);
    if (percent >= nextLogPercent || chunkIdx + 1 === count) {
      addLog(`${stepName}传输进度：${percent}% (${chunkIdx + 1}/${count} 包)`, '⇑');
      while (nextLogPercent <= percent) nextLogPercent += 10;
    }
  }

  return true;
}

async function handleDriverChange() {
  if (!isBleConnected()) return;
  await setDriver();
}

function waitForMemobusResponse(predicate, timeoutMs, description) {
  return new Promise((resolve, reject) => {
    const waiter = {
      predicate,
      resolve,
      reject,
      timer: setTimeout(() => {
        const index = tgzResponseWaiters.indexOf(waiter);
        if (index >= 0) tgzResponseWaiters.splice(index, 1);
        reject(new Error(`${description || '设备响应'}超时`));
      }, timeoutMs),
    };
    tgzResponseWaiters.push(waiter);
  });
}

function dispatchMemobusResponse(response) {
  if (response.group === 0x02 && response.function === 0x01 && response.status !== 0) {
    tgzImageErrorResponse = response;
  }
  if (response.group === 0x02 && response.function === 0x19 && response.status === 0) {
    applyTgzStorageInfo(response.body);
  }
  if (response.group === 0x02 && response.function === 0x1c && response.body.length >= 2) {
    const result = response.body[0];
    const progress = response.body[1];
    if (result === 2) setStatus('外置 Flash 正在擦除...');
    if (result === 3) setStatus(`外置 Flash 擦除进度 ${progress}%`);
    if (result === 4) {
      setStatus('外置 Flash 已擦除完成。');
      addLog('外置 Flash 已擦除完成。');
      void refreshTgzStorage();
    }
  }
  if (response.group === 0x02 && response.function === 0x15 && response.body[0] === 1) {
    setStatus('图片已发送，屏幕刷新中...');
  }

  for (let index = tgzResponseWaiters.length - 1; index >= 0; index--) {
    const waiter = tgzResponseWaiters[index];
    if (!waiter.predicate(response)) continue;
    tgzResponseWaiters.splice(index, 1);
    clearTimeout(waiter.timer);
    waiter.resolve(response);
  }
}

function handleTgzNotification(event) {
  try {
    const value = event.target.value;
    const packet = new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
    const frame = tgzRx.push(packet);
    if (!frame) return;
    dispatchMemobusResponse(MemobusClient.decodeMemobusFrame(frame));
  } catch (error) {
    console.error(error);
    addLog(`通知解析失败：${error.message || error}`);
  }
}

function waitForNativeNrfMessage(predicate, timeoutMs, description) {
  return new Promise((resolve, reject) => {
    const waiter = {
      predicate,
      resolve,
      reject,
      timer: setTimeout(() => {
        const index = nativeNrfWaiters.indexOf(waiter);
        if (index >= 0) nativeNrfWaiters.splice(index, 1);
        reject(new Error(`${description || 'nRF 设备响应'}超时`));
      }, timeoutMs),
    };
    nativeNrfWaiters.push(waiter);
  });
}

function dispatchNativeNrfMessage(message) {
  for (let index = nativeNrfWaiters.length - 1; index >= 0; index--) {
    const waiter = nativeNrfWaiters[index];
    if (!waiter.predicate(message)) continue;
    nativeNrfWaiters.splice(index, 1);
    clearTimeout(waiter.timer);
    waiter.resolve(message);
  }
}

function handleNativeNrfNotification(event) {
  const value = event.target.value;
  const data = new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
  const message = new TextDecoder().decode(data).replace(/\0+$/, '');
  applyNativePanelMessage(message);
  dispatchNativeNrfMessage(message);
  handleNotify(value, msgIndex++);
}

async function writeTgzFrame(frame, options = {}) {
  const characteristic = legacyEpdCharacteristic || epdCharacteristic;
  if (!characteristic || characteristic === nrfEpdCharacteristic)
    throw new Error('旧版 FFFF 控制通道不可用');
  let fast = options.fast !== false && tgzFastWriteEnabled &&
    characteristic.properties?.writeWithoutResponse &&
    typeof characteristic.writeValueWithoutResponse === 'function';
  const sequenceStart = tgzTxSequence;

  for (let candidate = tgzPacketLengthIndex; candidate < TGZ_PACKET_LENGTHS.length; candidate++) {
    const packetLength = TGZ_PACKET_LENGTHS[candidate];
    const packets = MemobusClient.fragmentBlufi(frame, packetLength, sequenceStart);
    let written = 0;
    try {
      for (let index = 0; index < packets.length; index++) {
        const forceResponse = fast && (
          tgzNoResponseRemaining === 0 || index === packets.length - 1
        );
        const useFast = fast && !forceResponse;
        const fastStillUsable = await writeTgzPacket(characteristic, packets[index], useFast);
        if (useFast && fastStillUsable) {
          tgzNoResponseRemaining--;
          await sleep(TGZ_WRITE_PACING_MS);
        } else {
          if (useFast) {
            fast = false;
            tgzFastWriteEnabled = false;
            addLog('快速写入被浏览器拒绝，已切换兼容写入。');
          }
          tgzNoResponseRemaining = TGZ_WRITE_RESPONSE_INTERVAL;
        }
        written++;
        tgzTxSequence = (tgzTxSequence + 1) & 0xff;
        if (options.onPacket) options.onPacket(index + 1, packets.length);
      }
      tgzPacketLengthIndex = candidate;
      document.getElementById('mtusize').value = packetLength;
      return;
    } catch (error) {
      if (written === 0 && candidate + 1 < TGZ_PACKET_LENGTHS.length) {
        tgzTxSequence = sequenceStart;
        addLog(`蓝牙包长 ${packetLength} 不兼容，尝试 ${TGZ_PACKET_LENGTHS[candidate + 1]} 字节`);
        await sleep(80);
        continue;
      }
      throw error;
    }
  }
  throw new Error('无法找到兼容的蓝牙包长');
}

async function requestTgz(group, fn, body = null, timeoutMs = 10000, description = '设备命令') {
  const responsePromise = waitForMemobusResponse(
    response => response.group === group && response.function === fn,
    timeoutMs,
    description
  );
  await writeTgzFrame(MemobusClient.encodeMemobusRequest(group, fn, 0, body));
  const response = await responsePromise;
  if (response.status !== 0) throw new Error(`${description}失败，状态 ${response.status}`);
  return response;
}

function applyTgzHandshake(response) {
  const fields = MemobusClient.decodeTlvs(response.body);
  const capabilities = fields[5];
  rleSupport = Boolean(capabilities && capabilities.length && (capabilities[0] & 0x01));
  firmwareVersion = {
    label: fields[4] ? new TextDecoder().decode(fields[4]) : 'TGZ-52811',
    ledControl: false,
    directImagePrepare: false,
    outdated: false,
  };
  addLog(`固件版本: ${firmwareVersion.label}`);
  addLog(rleSupport
    ? '固件已启用 RLE 压缩；1024 字节解压块连续发送'
    : '固件未声明 RLE 能力，使用原始传输');
}

function applyPanelId(panelId, transport = 'TGZ 离线 Web Bluetooth') {
  if (!TGZ_PANEL_NAMES[panelId]) throw new Error(`固件返回未知屏幕编号 ${panelId}`);
  tgzPanelId = panelId;
  const mode = panelId <= 2 ? 'fourColor' : 'sixColor';
  const driverSelect = document.getElementById('epddriver');
  driverSelect.value = String(panelId);
  document.getElementById('ditherMode').value = mode;
  document.getElementById('canvasSize').value = 'TGZ_760_528';
  updateCanvasSize({ reloadImage: false });
  updateDitcherOptions({ reloadImage: false });
  const label = `${TGZ_PANEL_NAMES[panelId]} · ${mode === 'fourColor' ? '四色' : '六色'}`;
  document.getElementById('driverMeta').textContent = `${label} · ${transport}`;
  addLog(`自动识别屏幕：${TGZ_PANEL_NAMES[panelId]}`);
  return panelId;
}

function applyTgzPanelStatus(response) {
  const panelId = response.body.length >= 2 ? response.body[1] : 0;
  return applyPanelId(panelId);
}

function applyNativePanelMessage(message) {
  const panelMatch = /(?:^|\s)panel=(\d+)/.exec(message);
  const mtuMatch = /(?:^|\s)mtu=(\d+)/.exec(message);
  if (mtuMatch) {
    nativeNrfMtu = Math.max(20, Math.min(247, parseInt(mtuMatch[1], 10)));
    document.getElementById('mtusize').value = nativeNrfMtu;
  }
  if (message.includes('rle=1')) rleSupport = true;
  return panelMatch ? applyPanelId(parseInt(panelMatch[1], 10), 'nRF 原生 BLE') : 0;
}

async function identifyTgzPanel() {
  return applyTgzPanelStatus(await requestTgz(0x02, 0x18, null, 15000, '屏幕识别'));
}

function readTgzLe16(data, offset) {
  return data[offset] | data[offset + 1] << 8;
}

function readTgzLe32(data, offset) {
  return (data[offset] | data[offset + 1] << 8 |
    data[offset + 2] << 16 | data[offset + 3] << 24) >>> 0;
}

function applyTgzStorageInfo(body) {
  if (body.length < 30) return;
  tgzStorageAvailable = (body[1] & 0x01) !== 0;
  const storeMode = (body[1] & 0x02) !== 0;
  const capacity = readTgzLe32(body, 8);
  const total = readTgzLe16(body, 16);
  const used = readTgzLe16(body, 18);
  const free = readTgzLe16(body, 20);
  const remaining = readTgzLe32(body, 22);
  tgzStorageFreeSlots = free;
  slotState.count = total;
  document.getElementById('slotRefreshAfterSave').checked = storeMode;
  document.getElementById('slotSummary').textContent = tgzStorageAvailable
    ? `外置 Flash ${formatSlotBytes(capacity)} · 已用 ${used}/${total} · 可存 ${free} 张`
    : '未识别到外置 Flash';
  document.getElementById('slotHint').textContent = tgzStorageAvailable
    ? `剩余 ${formatSlotBytes(remaining)}；保存模式下容量满会拒绝继续写入`
    : '直接显示仍可使用，保存模式不可用';
  updateButtonStatus();
}

async function refreshTgzStorage() {
  try {
    await requestTgz(0x02, 0x19, null, 10000, '读取 Flash 容量');
  } catch (error) {
    addLog(error.message || String(error));
  }
}

async function setTgzTransferMode(store) {
  if (store && !tgzStorageAvailable) throw new Error('未识别到可用外置 Flash');
  const response = await requestTgz(0x02, 0x1a, [store ? 1 : 0], 10000, '切换传图模式');
  document.getElementById('slotRefreshAfterSave').checked = response.body[0] === 1;
  return response;
}

async function eraseTgzStorage() {
  if (!tgzStorageAvailable || !confirm('确定擦除外置 Flash 中的全部图片吗？')) return;
  try {
    updateButtonStatus(true);
    await requestTgz(0x02, 0x1b, [0xa5], 10000, '擦除 Flash');
    setStatus('外置 Flash 正在擦除，请保持连接...');
    addLog('外置 Flash 已开始擦除，进度会由设备回报。');
  } catch (error) {
    addLog(error.message || String(error));
  } finally {
    updateButtonStatus();
  }
}

async function refreshStorage() {
  return nrfEpdCharacteristic ? refreshSlots(0) : refreshTgzStorage();
}

async function eraseStorage() {
  return nrfEpdCharacteristic ? freeAllImageSlots() : eraseTgzStorage();
}

async function setDriver(options = {}) {
  updateButtonStatus(true);
  const driverSelect = document.getElementById("epddriver");
  driverSelect.disabled = true;

  try {
    const panelId = Number.parseInt(driverSelect.value, 10);
    if (!Number.isInteger(panelId) || panelId < 0 || panelId > 5) {
      throw new Error('屏幕驱动编号无效');
    }
    const response = await requestTgz(0x02, 0x18, [panelId], 60000, '驱动切换');
    const activePanel = applyTgzPanelStatus(response);
    addLog(panelId === 0
      ? `自动识别完成：${TGZ_PANEL_NAMES[activePanel]}`
      : `驱动已切换：${TGZ_PANEL_NAMES[activePanel]}`);
  } finally {
    driverSelect.disabled = false;
    updateButtonStatus();
  }
}

async function setLedEnabled() {
  const ledToggle = document.getElementById('ledEnabled');
  const enabled = ledToggle.checked;

  if (!isBleConnected() || !firmwareVersion.ledControl) {
    ledToggle.checked = !enabled;
    addLog('当前固件不支持 LED 开关，请升级到 0x40 或更高版本。');
    updateButtonStatus();
    return;
  }

  ledToggle.disabled = true;
  if (await write(EpdCmd.SET_LED, buildLedPayload(enabled))) {
    addLog(enabled ? 'LED ON' : 'LED OFF');
  } else {
    ledToggle.checked = !enabled;
  }
  updateButtonStatus();
}

async function setLedTransferChase() {
  const checkbox = document.getElementById('ledTransferChase');
  const chase = checkbox.checked;

  if (!isBleConnected() || !firmwareVersion.ledControl) {
    checkbox.checked = !chase;
    updateButtonStatus();
    return;
  }

  checkbox.disabled = true;
  if (await write(EpdCmd.SET_LED, buildLedPayload())) {
    addLog(chase ? '传输灯效：彩色跑马灯' : '传输灯效：彩色呼吸灯');
  } else {
    checkbox.checked = !chase;
  }
  updateButtonStatus();
}

function clampLedChannel(value) {
  const parsed = Number.parseInt(value, 10);
  return Number.isFinite(parsed) ? Math.max(0, Math.min(255, parsed)) : 0;
}

function getLedRgb() {
  return {
    red: clampLedChannel(document.getElementById('ledRed').value),
    green: clampLedChannel(document.getElementById('ledGreen').value),
    blue: clampLedChannel(document.getElementById('ledBlue').value)
  };
}

function ledBrightnessToByte() {
  const parsed = Number.parseInt(document.getElementById('ledBrightness').value, 10);
  const percent = Number.isFinite(parsed) ? Math.max(1, Math.min(100, parsed)) : 2;
  return Math.max(1, Math.min(255, Math.round(percent * 255 / 100)));
}

function buildLedPayload(enabled = document.getElementById('ledEnabled').checked) {
  const rgb = getLedRgb();
  const chase = document.getElementById('ledTransferChase').checked;
  const brightness = ledBrightnessToByte();
  return new Uint8Array([enabled ? 1 : 0, rgb.red, rgb.green, rgb.blue, chase ? 0 : 1, brightness]);
}

function ledRgbToHex(red, green, blue) {
  return `#${[red, green, blue].map((value) => clampLedChannel(value).toString(16).padStart(2, '0')).join('')}`.toUpperCase();
}

function ledHexToRgb(hex) {
  const match = /^#?([0-9a-f]{6})$/i.exec(hex || '');
  if (!match) return null;
  return {
    red: parseInt(match[1].slice(0, 2), 16),
    green: parseInt(match[1].slice(2, 4), 16),
    blue: parseInt(match[1].slice(4, 6), 16)
  };
}

function setLedRgb(red, green, blue, scheduleWrite = false) {
  const values = [clampLedChannel(red), clampLedChannel(green), clampLedChannel(blue)];
  const channels = ['Red', 'Green', 'Blue'];
  channels.forEach((channel, index) => {
    const range = document.getElementById(`led${channel}`);
    range.value = String(values[index]);
    document.getElementById(`led${channel}Value`).value = String(values[index]);
    updateRangeFill(range);
  });

  const hex = ledRgbToHex(...values);
  document.getElementById('ledColorHex').textContent = hex;
  document.getElementById('ledColorSwatch').style.backgroundColor = hex;
  document.getElementById('ledCustomColor').value = hex.toLowerCase();
  if (scheduleWrite) scheduleLedColorWrite();
}

function setLedBrightness(percent, scheduleWrite = false) {
  const brightness = Math.max(1, Math.min(100, Number.parseInt(percent, 10) || 2));
  const range = document.getElementById('ledBrightness');
  range.value = String(brightness);
  document.getElementById('ledBrightnessValue').value = `${brightness}%`;
  updateRangeFill(range);
  if (scheduleWrite) scheduleLedColorWrite();
}

async function writeLedColor() {
  if (!isBleConnected() || !firmwareVersion.ledControl) return;
  await write(EpdCmd.SET_LED, buildLedPayload());
}

function scheduleLedColorWrite() {
  clearTimeout(ledColorWriteTimer);
  ledColorWriteTimer = setTimeout(() => { void writeLedColor(); }, LED_COLOR_WRITE_DELAY_MS);
}

function closeLedColorPopover() {
  const button = document.getElementById('ledColorButton');
  const popover = document.getElementById('ledColorPopover');
  popover.hidden = true;
  button.setAttribute('aria-expanded', 'false');
}

function initLedColorControl() {
  const control = document.querySelector('.led-color-control');
  const button = document.getElementById('ledColorButton');
  const popover = document.getElementById('ledColorPopover');
  const customColor = document.getElementById('ledCustomColor');

  button.addEventListener('click', () => {
    if (button.disabled) return;
    const open = popover.hidden;
    popover.hidden = !open;
    button.setAttribute('aria-expanded', String(open));
  });

  document.querySelectorAll('[data-led-color]').forEach((preset) => {
    preset.addEventListener('click', () => {
      const rgb = ledHexToRgb(preset.dataset.ledColor);
      if (rgb) setLedRgb(rgb.red, rgb.green, rgb.blue, true);
    });
  });

  customColor.addEventListener('input', () => {
    const rgb = ledHexToRgb(customColor.value);
    if (rgb) setLedRgb(rgb.red, rgb.green, rgb.blue, true);
  });

  ['Red', 'Green', 'Blue'].forEach((channel) => {
    document.getElementById(`led${channel}`).addEventListener('input', () => {
      const rgb = getLedRgb();
      setLedRgb(rgb.red, rgb.green, rgb.blue, true);
    });
  });

  document.getElementById('ledBrightness').addEventListener('input', (event) => {
    setLedBrightness(event.target.value, true);
  });

  document.addEventListener('click', (event) => {
    if (!popover.hidden && !control.contains(event.target)) closeLedColorPopover();
  });
  document.addEventListener('keydown', (event) => {
    if (event.key === 'Escape' && !popover.hidden) {
      closeLedColorPopover();
      button.focus();
    }
  });
  setLedRgb(0, 0, 255);
  setLedBrightness(2);
}

function getWeekStart() {
  const weekStart = document.getElementById('weekStart');
  const value = weekStart ? parseInt(weekStart.value, 10) : 0;
  return Number.isInteger(value) && value >= 0 && value <= 6 ? value : 0;
}

function buildTimeData(mode) {
  const timestamp = Math.floor(new Date().getTime() / 1000);
  return new Uint8Array([
    (timestamp >> 24) & 0xFF,
    (timestamp >> 16) & 0xFF,
    (timestamp >> 8) & 0xFF,
    timestamp & 0xFF,
    -(new Date().getTimezoneOffset() / 60),
    mode
  ]);
}

async function sendTimeCommand(mode, modeName) {
  const weekStart = getWeekStart();
  if (!await write(EpdCmd.SET_WEEK_START, new Uint8Array([weekStart]))) return false;

  if (await write(EpdCmd.SET_TIME, buildTimeData(mode))) {
    addLog(`${modeName}已同步！`);
    addLog("屏幕刷新完成前请不要操作。");
    return true;
  }
  return false;
}

async function syncTime(mode) {
  if (mode === 2) {
    if (!confirm('提醒：时钟模式目前使用全刷实现，此功能目前多用于修复老化屏残影问题，不建议长期开启，是否继续？')) return;
  }
  await sendTimeCommand(mode, mode === 1 ? '日历模式' : '时钟模式');
}

async function clearScreen() {
  if (confirm('确认清除屏幕内容?')) {
    await write(EpdCmd.CLEAR);
    addLog("清屏指令已发送！");
    addLog("屏幕刷新完成前请不要操作。");
  }
}

async function sendcmd() {
  const cmdTXT = document.getElementById('cmdTXT').value;
  if (cmdTXT == '') return;
  const bytes = hex2bytes(cmdTXT);
  await write(bytes[0], bytes.length > 1 ? bytes.slice(1) : null);
}

function convertUC8159(blackWhiteData, redWhiteData) {
  const halfLength = blackWhiteData.length;
  let payloadData = new Uint8Array(halfLength * 4);
  let payloadIdx = 0;
  let black_data, color_data, data;
  for (let i = 0; i < halfLength; i++) {
    black_data = blackWhiteData[i];
    color_data = redWhiteData[i];
    for (let j = 0; j < 8; j++) {
      if ((color_data & 0x80) == 0x00) data = 0x04;  // red
      else if ((black_data & 0x80) == 0x00) data = 0x00;  // black
      else data = 0x03;  // white
      data = (data << 4) & 0xFF;
      black_data = (black_data << 1) & 0xFF;
      color_data = (color_data << 1) & 0xFF;
      j++;
      if ((color_data & 0x80) == 0x00) data |= 0x04;  // red
      else if ((black_data & 0x80) == 0x00) data |= 0x00;  // black
      else data |= 0x03;  // white
      black_data = (black_data << 1) & 0xFF;
      color_data = (color_data << 1) & 0xFF;
      payloadData[payloadIdx++] = data;
    }
  }
  return payloadData;
}



function isGDEM037F51Driver(selectElement) {
  const option = selectElement.options[selectElement.selectedIndex];
  const value = (selectElement.value || '').toLowerCase();
  const size = option ? option.getAttribute('data-size') : '';
  const label = option ? option.textContent : '';
  return value === '0d' || size === '3.7_416_240' && label.includes('GDEM037F51');
}

function isGDEY037Z03Driver(selectElement) {
  const option = selectElement.options[selectElement.selectedIndex];
  const value = (selectElement.value || '').toLowerCase();
  const size = option ? option.getAttribute('data-size') : '';
  const label = option ? option.textContent : '';
  return value === '0e' || value === '0f' || value === '12' ||
    size === '3.7_416_240' && (label.includes('GDEY037Z03') || label.includes('YS4370JS0C3') || label.includes('LG 3.7'));
}

function isSSD1619_213_250x122Driver(selectElement) {
  return (selectElement.value || '').toLowerCase() === '19';
}

function get1bppPixel(data, width, x, y) {
  const byteIndex = y * Math.ceil(width / 8) + Math.floor(x / 8);
  const shift = 7 - (x & 0x07);
  return (data[byteIndex] >> shift) & 0x01;
}

function set1bppPixel(data, width, x, y, value) {
  const byteIndex = y * Math.ceil(width / 8) + Math.floor(x / 8);
  const mask = 0x80 >> (x & 0x07);
  if (value) data[byteIndex] |= mask;
  else data[byteIndex] &= ~mask;
}

function convertGDEY037Z03Plane(data, srcWidth = canvas.width, srcHeight = canvas.height) {
  const nativeWidth = 240;
  const nativeHeight = 416;

  if (srcWidth === nativeWidth && srcHeight === nativeHeight) {
    return new Uint8Array(data);
  }

  if (srcWidth !== nativeHeight || srcHeight !== nativeWidth) {
    return new Uint8Array(data);
  }

  const output = new Uint8Array((nativeWidth * nativeHeight) / 8).fill(0xFF);
  for (let y = 0; y < srcHeight; y++) {
    for (let x = 0; x < srcWidth; x++) {
      set1bppPixel(output, nativeWidth, y, nativeHeight - 1 - x, get1bppPixel(data, srcWidth, x, y));
    }
  }

  return output;
}

function convertSSD1619_213_250x122Plane(data, srcWidth = canvas.width, srcHeight = canvas.height) {
  const nativeWidth = 128;
  const nativeHeight = 250;
  if (srcWidth !== 250 || srcHeight !== 122) return new Uint8Array(data);

  const output = new Uint8Array((nativeWidth * nativeHeight) / 8).fill(0xFF);
  for (let y = 0; y < srcHeight; y++) {
    for (let x = 0; x < srcWidth; x++) {
      set1bppPixel(output, nativeWidth, y, nativeHeight - 1 - x,
        get1bppPixel(data, srcWidth, x, y));
    }
  }
  return output;
}

function get2bppPixel(data, width, x, y) {
  const pixelIndex = y * width + x;
  const byteIndex = pixelIndex >> 2;
  const shift = 6 - ((pixelIndex & 0x03) * 2);
  return (data[byteIndex] >> shift) & 0x03;
}

function set2bppPixel(data, width, x, y, value) {
  const pixelIndex = y * width + x;
  const byteIndex = pixelIndex >> 2;
  const shift = 6 - ((pixelIndex & 0x03) * 2);
  data[byteIndex] = (data[byteIndex] & ~(0x03 << shift)) | ((value & 0x03) << shift);
}

function encodeNativeSlotAction(action, slot) {
  const payload = new Uint8Array(5);
  payload[0] = action & 0xff;
  payload.set(encodeUint32LE(slot >>> 0), 1);
  return payload;
}

async function prepareNativeNrfTransfer(store, slot, refreshAfterSave) {
  const requested = store ? slot : 0xFFFFFFFF;
  const ready = waitForNativeNrfMessage(
    message => message === 'ready=1' || message.startsWith('slot_error='),
    95000,
    store ? '槽位擦除准备' : '直接显示准备'
  );
  await writeNativeNrfPayload(new Uint8Array([
    EpdCmd.SET_SLOT,
    ...encodeNativeSlotAction(0, requested),
  ]), false);
  const response = await ready;
  if (response !== 'ready=1') throw new Error(`槽位准备失败：${response}`);

  if (store) {
    await writeNativeNrfPayload(new Uint8Array([
      EpdCmd.SET_SLOT,
      ...encodeNativeSlotAction(refreshAfterSave ? 3 : 2, slot),
    ]), false);
  }
}

async function writeNativeNrfImage(packedPixels, mode) {
  const raw = packedPixels instanceof Uint8Array
    ? packedPixels
    : new Uint8Array(packedPixels);
  const encoded = rleEncode(raw);
  const useRle = rleSupport && encoded.length < raw.length;
  const transfer = useRle ? encoded : raw;
  const chunkSize = Math.max(18, Math.min(245, nativeNrfMtu - 2));
  const packetCount = Math.ceil(transfer.length / chunkSize);
  const receipt = waitForNativeNrfMessage(
    message => message === 'image=received' ||
      message.startsWith('image_error=') || message.startsWith('slot_error='),
    45000,
    '图片完整接收确认'
  );

  addLog(useRle
    ? `nRF RLE 压缩：${raw.length} -> ${transfer.length} 字节 (${(transfer.length * 100 / raw.length).toFixed(1)}%)`
    : `nRF 原始传输：${raw.length} 字节`);
  addLog(`开始发送：${mode === 'fourColor' ? '四色' : '六色'}，${packetCount} 个 ATT 分包`);
  const startedAt = performance.now();

  for (let index = 0; index < packetCount; index++) {
    const chunk = transfer.slice(index * chunkSize, (index + 1) * chunkSize);
    const flags = (index === 0 ? 0x02 : 0x00) | (useRle ? 0x04 : 0x00);
    const packet = new Uint8Array(2 + chunk.length);
    packet[0] = EpdCmd.WRITE_IMG;
    packet[1] = flags;
    packet.set(chunk, 2);

    const preferFast = nativeNrfNoResponseRemaining > 0;
    const fastUsed = await writeNativeNrfPayload(packet, preferFast);
    if (preferFast && fastUsed) {
      nativeNrfNoResponseRemaining--;
      await sleep(NATIVE_NRF_WRITE_PACING_MS);
    } else {
      nativeNrfNoResponseRemaining = NATIVE_NRF_WRITE_RESPONSE_INTERVAL;
    }

    const exactProgress = Math.min(99, (index + 1) * 100 / packetCount);
    const percent = Math.floor(exactProgress);
    setStatus(`正在传输 ${percent}% · ${index + 1}/${packetCount}`);
    updateTgzTransferOverlay(exactProgress);
  }

  updateTgzTransferOverlay(100);
  setStatus('图片数据已发送，设备正在写入 Flash...');
  addLog(`${packetCount} 个 ATT 分包已写入 BLE，用时 ${((performance.now() - startedAt) / 1000).toFixed(1)} 秒`);
  const response = await receipt;
  if (response !== 'image=received') throw new Error(`设备拒绝图像：${response}`);
  addLog(`设备已完整接收图片，总用时 ${((performance.now() - startedAt) / 1000).toFixed(1)} 秒`);
}


function mapGDEM037F51Color(value) {
  return value & 0x03;
}
function convertGDEM037F51(data, srcWidth = canvas.width, srcHeight = canvas.height) {
  const nativeWidth = 240;
  const nativeHeight = 416;

  if (srcWidth === nativeWidth && srcHeight === nativeHeight) {
    const output = new Uint8Array(data.length);
    for (let y = 0; y < srcHeight; y++) {
      for (let x = 0; x < srcWidth; x++) {
        set2bppPixel(output, srcWidth, x, y, mapGDEM037F51Color(get2bppPixel(data, srcWidth, x, y)));
      }
    }
    return output;
  }

  if (srcWidth !== nativeHeight || srcHeight !== nativeWidth) {
    return new Uint8Array(data);
  }

  const output = new Uint8Array((nativeWidth * nativeHeight) / 4);
  for (let y = 0; y < srcHeight; y++) {
    for (let x = 0; x < srcWidth; x++) {
      const value = mapGDEM037F51Color(get2bppPixel(data, srcWidth, x, y));
      set2bppPixel(output, nativeWidth, srcHeight - 1 - y, x, value);
    }
  }

  return output;
}
async function writeTgzImage(imageData, mode) {
  const packed = MemobusClient.packOfficialPalettePixels(imageData, mode, {
    mirrorHorizontal: true,
  });
  const imageOptions = {
    width: 760,
    height: 528,
    chunkSize: TGZ_RLE_CHUNK_SIZE,
    packetBase: 1,
  };
  const sourceBytes = packed.length + 8;
  let transfer = rleSupport
    ? MemobusClient.createOptimizedImageTransfer(packed, imageOptions)
    : null;
  if (!transfer || !transfer.compressed) {
    transfer = {
      requests: MemobusClient.createImageRequests(packed, {
        width: 760,
        height: 528,
        chunkSize: 4096,
        packetBase: 1,
      }),
      compressed: false,
      sourceBytes,
      transferBytes: sourceBytes,
    };
  }

  if (transfer.compressed) {
    const ratio = transfer.transferBytes / transfer.sourceBytes * 100;
    addLog(`RLE 压缩：${transfer.sourceBytes} -> ${transfer.transferBytes} 字节 (${ratio.toFixed(1)}%)`);
  } else {
    addLog(`使用原始传输：${transfer.sourceBytes} 字节`);
  }
  addLog(`开始发送：${mode === 'fourColor' ? '四色' : '六色'}，${transfer.requests.length} 个图像分包`);

  tgzImageErrorResponse = null;
  const startedAt = performance.now();
  let finalAckPromise = null;
  for (let index = 0; index < transfer.requests.length; index++) {
    if (index === transfer.requests.length - 1) {
      finalAckPromise = waitForMemobusResponse(
        response => response.group === 0x02 && response.function === 0x01,
        45000,
        '图像完整接收确认'
      );
    }
    await writeTgzFrame(transfer.requests[index], {
      fast: true,
      onPacket(completed, total) {
        const frameProgress = index + completed / total;
        const exactProgress = Math.min(99, frameProgress / transfer.requests.length * 99);
        const percent = Math.floor(exactProgress);
        setStatus(`正在传输 ${percent}% · ${index + 1}/${transfer.requests.length}`);
        updateTgzTransferOverlay(exactProgress);
      },
    });
    if (tgzImageErrorResponse) {
      throw new Error(`设备拒绝图像，状态 ${tgzImageErrorResponse.status}`);
    }
  }

  const writtenSeconds = (performance.now() - startedAt) / 1000;
  addLog(`${transfer.requests.length} 个图像分包已写入 BLE，用时 ${writtenSeconds.toFixed(1)} 秒`);
  setStatus('设备正在校验并写入 Flash...');
  const finalAck = await finalAckPromise;
  if (finalAck.status !== 0) throw new Error(`设备拒绝图像，状态 ${finalAck.status}`);
  updateTgzTransferOverlay(100);
  setStatus('传输完成，屏幕刷新中...');
  addLog(`设备已完整接收图片，总用时 ${((performance.now() - startedAt) / 1000).toFixed(1)} 秒`);
}

async function sendimgNative(options = {}) {
  if (cropManager) cropManager.commitPendingTransform(false);
  if (canvas.width !== TGZ_WIDTH || canvas.height !== TGZ_HEIGHT)
    throw new Error(`TGZ 固件只接受 ${TGZ_WIDTH}×${TGZ_HEIGHT} 画布`);

  const mode = tgzPanelId <= 2 ? 'fourColor' : 'sixColor';
  document.getElementById('ditherMode').value = mode;
  const processedData = processCanvasImageData();
  const finalImageData = decodeProcessedData(processedData, canvas.width, canvas.height, mode);
  const packedPixels = MemobusClient.packOfficialPalettePixels(finalImageData, mode, {
    mirrorHorizontal: true,
  });
  const requestedSlot = Number.isInteger(options.slot) ? options.slot : null;
  const storeRequested = requestedSlot != null || document.getElementById('slotRefreshAfterSave').checked;
  const targetSlot = requestedSlot != null
    ? requestedSlot
    : (storeRequested ? await findFirstFreeNativeSlot() : null);
  if (storeRequested && targetSlot == null)
    throw new Error('外置 Flash 容量已满，已拒绝继续保存');

  const refreshAfterSave = storeRequested && options.refreshAfterSave === true;
  if (storeRequested) cacheCurrentSlotPreview(targetSlot, processedData, mode);
  await prepareNativeNrfTransfer(storeRequested, targetSlot, refreshAfterSave);
  const ready = !storeRequested || refreshAfterSave
    ? waitForNativeNrfMessage(message => message === 'ready=1' || message.startsWith('display_error='),
      95000, '屏幕刷新完成')
    : null;
  await writeNativeNrfImage(packedPixels, mode);

  if (storeRequested) {
    await refreshSlots(Math.floor(targetSlot / SLOT_PAGE_SIZE) * SLOT_PAGE_SIZE);
    if (refreshAfterSave) {
      const response = await ready;
      if (response !== 'ready=1') throw new Error(`屏幕刷新失败：${response}`);
      setStatus(`槽位 ${targetSlot + 1} 已保存并刷新。`);
    } else {
      setStatus(`图片已保存到槽位 ${targetSlot + 1}，可用设备按键切换。`);
    }
  } else {
    setStatus('传输完成，屏幕刷新中...');
    const response = await ready;
    if (response !== 'ready=1') throw new Error(`屏幕刷新失败：${response}`);
    setStatus('屏幕刷新完成。');
  }
  return true;
}

async function sendimg(options = {}) {
  if (!isBleConnected() || imageTransferActive) return false;
  if (cropManager) cropManager.commitPendingTransform(false);
  if (canvas.width !== TGZ_WIDTH || canvas.height !== TGZ_HEIGHT) {
    addLog(`TGZ 固件只接受 ${TGZ_WIDTH}×${TGZ_HEIGHT} 画布。`);
    return false;
  }

  imageTransferActive = true;
  startTime = new Date().getTime();
  updateButtonStatus();
  showTgzTransferOverlay();
  try {
    if (nrfEpdCharacteristic) {
      const result = await sendimgNative(options);
      await sleep(500);
      hideTgzTransferOverlay();
      return result;
    }
    const mode = tgzPanelId <= 2 ? 'fourColor' : 'sixColor';
    document.getElementById('ditherMode').value = mode;
    const processedData = processCanvasImageData();
    const finalImageData = decodeProcessedData(processedData, canvas.width, canvas.height, mode);
    const store = document.getElementById('slotRefreshAfterSave').checked;
    if (store) {
      await refreshTgzStorage();
      if (tgzStorageFreeSlots === 0) throw new Error('外置 Flash 容量已满，已拒绝继续保存');
    }
    await setTgzTransferMode(store);
    await writeTgzImage(finalImageData, mode);
    if (store) {
      setStatus('图片已保存到外置 Flash，可用按键切换。');
      await refreshTgzStorage();
    }
    await sleep(700);
    hideTgzTransferOverlay();
    return true;
  } catch (error) {
    console.error(error);
    setStatus(`传输失败：${error.message || error}`);
    addLog(`传输失败：${error.message || error}`);
    hideTgzTransferOverlay();
    if (bleDevice && bleDevice.gatt && bleDevice.gatt.connected) bleDevice.gatt.disconnect();
    return false;
  } finally {
    imageTransferActive = false;
    updateButtonStatus();
  }
}

async function sendimgLegacy(options = {}) {
  if (cropManager) cropManager.commitPendingTransform(false);
  const canvasSize = document.getElementById('canvasSize').value;
  const ditherMode = document.getElementById('ditherMode').value;
  const epdDriverSelect = document.getElementById('epddriver');
  const selectedOption = epdDriverSelect.options[epdDriverSelect.selectedIndex];

  if (selectedOption.getAttribute('data-size') !== canvasSize) {
    if (!confirm("警告：画布尺寸和驱动不匹配，是否继续？")) return;
  }
  if (selectedOption.getAttribute('data-color') !== ditherMode) {
    if (!confirm("警告：颜色模式和驱动不匹配，是否继续？")) return;
  }

  displayErrorActive = false;
  startTime = new Date().getTime();
  const status = document.getElementById("status");
  status.parentElement.style.display = "block";

  const processedData = processCanvasImageData();

  imageTransferActive = true;
  updateButtonStatus();
  const targetSlot = Number.isInteger(options.slot) ? options.slot : null;
  const directPrepare = targetSlot == null &&
    epdDriverSelect.value.toLowerCase() === '1a' && firmwareVersion.directImagePrepare;
  const refreshAfterSave = targetSlot != null && options.refreshAfterSave === true;
  if (targetSlot != null) {
    cacheCurrentSlotPreview(targetSlot, processedData, ditherMode);
    if (targetSlot < 0 || targetSlot >= slotState.count ||
      !await write(EpdCmd.SET_SLOT, encodeSlotAction(0, targetSlot))) {
      addLog('槽位写入准备失败。');
      removeSlotImageCache(targetSlot);
      imageTransferActive = false;
      updateButtonStatus();
      return false;
    }
    setStatus(`正在写入槽位 ${targetSlot + 1}...`);
  }

  let transferOk = true;

  if (ditherMode === 'sevenColor') {
    transferOk = await writeImage(processedData, 'bw', directPrepare);
  } else if (ditherMode === 'fourColor') {
    const useGDEM037F51 = isGDEM037F51Driver(epdDriverSelect);
    const imagePayload = useGDEM037F51 ? convertGDEM037F51(processedData, canvas.width, canvas.height) : processedData;
    if (useGDEM037F51) addLog('3.7BWRY 图像数据已按日历方向重排为原生 240x416');
    transferOk = await writeImage(imagePayload, 'bw', directPrepare);
  } else if (ditherMode === 'threeColor') {
    const halfLength = Math.floor(processedData.length / 2);
    let blackWhiteData = processedData.slice(0, halfLength);
    let redWhiteData = processedData.slice(halfLength);
    if (isGDEY037Z03Driver(epdDriverSelect)) {
      blackWhiteData = convertGDEY037Z03Plane(blackWhiteData, canvas.width, canvas.height);
      redWhiteData = convertGDEY037Z03Plane(redWhiteData, canvas.width, canvas.height);
      addLog('3.7BWR 图像数据已按日历方向重排为原生 240x416');
    }
    if (isSSD1619_213_250x122Driver(epdDriverSelect)) {
      blackWhiteData = convertSSD1619_213_250x122Plane(blackWhiteData, canvas.width, canvas.height);
      redWhiteData = convertSSD1619_213_250x122Plane(redWhiteData, canvas.width, canvas.height);
      addLog('2.13寸图像数据已按 128x250 显存旋转并应用 X + 8 px 偏移');
    }
    if (epdDriverSelect.value === '08' || epdDriverSelect.value === '09') {
      transferOk = await writeImage(convertUC8159(blackWhiteData, redWhiteData), 'bw', directPrepare);
    } else {
      transferOk = await writeImage(blackWhiteData, 'bw', directPrepare);
      if (transferOk) transferOk = await writeImage(redWhiteData, 'red');
    }
  } else if (ditherMode === 'blackWhiteColor') {
    if (epdDriverSelect.value === '08' || epdDriverSelect.value === '09') {
      const emptyData = new Uint8Array(processedData.length).fill(0xFF);
      transferOk = await writeImage(convertUC8159(processedData, emptyData), 'bw', directPrepare);
    } else {
      transferOk = await writeImage(processedData, 'bw', directPrepare);
    }
  } else {
    addLog("当前固件不支持此颜色模式。");
    if (targetSlot != null) removeSlotImageCache(targetSlot);
    imageTransferActive = false;
    updateButtonStatus();
    return false;
  }

  if (!transferOk) {
    if (targetSlot != null) await write(EpdCmd.SET_SLOT, encodeSlotAction(0, 0xFFFFFFFF));
    if (targetSlot != null) removeSlotImageCache(targetSlot);
    setStatus('图片发送失败。');
    imageTransferActive = false;
    updateButtonStatus();
    return false;
  }

  const sendTime = (new Date().getTime() - startTime) / 1000.0;
  const savingSlot = targetSlot != null;
  addLog(savingSlot
    ? `图片数据发送完成！耗时: ${sendTime}s，正在提交槽位。`
    : `图片数据发送完成！耗时: ${sendTime}s，等待屏幕刷新。`);
  setStatus(savingSlot ? '图片数据发送完成，正在保存槽位...' : '图片数据发送完成，正在刷新屏幕...');
  startImageRefreshWait(targetSlot != null ? 'slot' : 'refresh');
  const completionSent = savingSlot
    ? await write(EpdCmd.SET_SLOT, encodeSlotAction(refreshAfterSave ? 3 : 2, targetSlot))
    : await write(EpdCmd.REFRESH);
  if (!completionSent) {
    cancelImageRefreshWait();
    if (targetSlot != null) removeSlotImageCache(targetSlot);
    setStatus(savingSlot ? '槽位提交命令发送失败。' : '刷新命令发送失败。');
    imageTransferActive = false;
    updateButtonStatus();
    return false;
  }
  return true;
}

function downloadDataArray() {
  if (cropManager) cropManager.commitPendingTransform(false);
  const mode = document.getElementById('ditherMode').value;
  const processedData = processCanvasImageData();

  if (mode === 'sixColor' && processedData.length !== canvas.width * canvas.height) {
    console.log(`错误：预期${canvas.width * canvas.height}字节，但得到${processedData.length}字节`);
    addLog('数组大小不匹配。请检查图像尺寸和模式。');
    return;
  }

  const dataLines = [];
  for (let i = 0; i < processedData.length; i++) {
    const hexValue = (processedData[i] & 0xff).toString(16).padStart(2, '0');
    dataLines.push(`0x${hexValue}`);
  }

  const formattedData = [];
  for (let i = 0; i < dataLines.length; i += 16) {
    formattedData.push(dataLines.slice(i, i + 16).join(', '));
  }

  const colorModeValue = mode === 'sixColor' ? 0 : mode === 'fourColor' ? 1 : mode === 'blackWhiteColor' ? 2 : 3;
  const arrayContent = [
    'const uint8_t imageData[] PROGMEM = {',
    formattedData.join(',\n'),
    '};',
    `const uint16_t imageWidth = ${canvas.width};`,
    `const uint16_t imageHeight = ${canvas.height};`,
    `const uint8_t colorMode = ${colorModeValue};`
  ].join('\n');

  const blob = new Blob([arrayContent], { type: 'text/plain' });
  const link = document.createElement('a');
  link.download = 'imagedata.h';
  link.href = URL.createObjectURL(blob);
  link.click();
  URL.revokeObjectURL(link.href);
}

function updateButtonStatus(forceDisabled = imageTransferActive || slotActionPending || slotReadState !== null || otaBusy) {
  const connected = gattServer != null && gattServer.connected;
  const canReconnect = bleDevice != null && bleDevice.gatt && !bleDevice.gatt.connected;
  const disabled = forceDisabled || !connected;
  document.getElementById("connectbutton").disabled = otaBusy;
  document.getElementById("reconnectbutton").disabled = otaBusy || reconnectActive || forceDisabled || !canReconnect;
  document.getElementById("sendimgbutton").disabled = disabled || tgzPanelId === 0;
  document.getElementById("setDriverbutton").disabled = disabled || !legacyEpdCharacteristic;
  document.getElementById("epddriver").disabled = disabled || !legacyEpdCharacteristic;
  document.getElementById("ledEnabled").disabled = true;
  const ledColorDisabled = true;
  document.getElementById('ledTransferChase').disabled = ledColorDisabled;
  document.getElementById("ledColorButton").disabled = ledColorDisabled;
  document.querySelector('.led-color-control').classList.toggle('is-disabled', ledColorDisabled);
  document.querySelectorAll('#ledColorPopover input, #ledColorPopover button').forEach((control) => {
    control.disabled = ledColorDisabled;
  });
  if (ledColorDisabled) closeLedColorPopover();
  document.getElementById('slotRefreshAfterSave').disabled = disabled || !tgzStorageAvailable;
  document.getElementById("refreshSlotsButton").disabled = disabled;
  document.getElementById("eraseAllSlotsButton").disabled = disabled || !tgzStorageAvailable;
  document.getElementById("startSlotSlideButton").disabled = true;
  document.getElementById("randomSlotSlideButton").disabled = true;
  document.getElementById("stopSlotSlideButton").disabled = true;
  document.getElementById('otaPanelToggle').disabled = true;
}

function finishDisconnect(message = '已断开连接.') {
  const hadConnectionState = gattServer || epdService || epdCharacteristic ||
    (bleDevice && bleDevice.gatt && bleDevice.gatt.connected);
  const enteringOta = otaPhase === 'entering';
  resetVariables({ clearLog: false });
  document.getElementById("connectbutton").innerHTML = '连接';
  updateButtonStatus();
  if (enteringOta && hadConnectionState) {
    setOtaStatus('设备正在启动 DfuTarg...', 0);
    addLog('应用连接已断开，正在启动 DfuTarg。');
  } else if (message && hadConnectionState) {
    addLog(message);
  }
}

function disconnect() {
  finishDisconnect('已断开连接.');
}

async function disconnectDevice() {
  const device = bleDevice;
  updateButtonStatus(true);
  try {
    if (device && device.gatt && device.gatt.connected) {
      addLog('正在断开蓝牙连接...');
      device.gatt.disconnect();
      await sleep(200);
    }
  } catch (e) {
    console.error(e);
    if (e.message) addLog('disconnect: ' + e.message);
  }
  finishDisconnect('已断开连接.');
}

function disconnectDeviceOnPageExit() {
  if (pageExitDisconnecting) return;
  pageExitDisconnecting = true;

  const device = bleDevice;
  try {
    if (otaClient) otaClient.cancel();
    if (device && device.gatt && device.gatt.connected) {
      device.gatt.disconnect();
    }
  } catch (e) {
    console.error(e);
  }
}

async function disconnectStaleBleConnections() {
  if (!navigator.bluetooth || typeof navigator.bluetooth.getDevices !== 'function') return;

  try {
    const devices = await navigator.bluetooth.getDevices();
    let disconnected = false;
    for (const device of devices) {
      const isEpdDevice = device && (device.name || '').startsWith('Lenmory');
      if (isEpdDevice && device.gatt && device.gatt.connected) {
        device.gatt.disconnect();
        disconnected = true;
      }
    }
    if (disconnected) addLog('已清理刷新前遗留的蓝牙连接。');
  } catch (e) {
    console.error(e);
  }
}

async function preConnect() {
  const connected = (gattServer && gattServer.connected) ||
    (bleDevice && bleDevice.gatt && bleDevice.gatt.connected) ||
    epdCharacteristic != null;
  if (connected) {
    await disconnectDevice();
    return;
  }
  else {
    resetVariables();
    try {
      addLog("正在扫描墨水屏蓝牙设备...");
      bleDevice = await navigator.bluetooth.requestDevice({
        filters: [
          { services: [NRF_EPD_SERVICE_UUID] },
          { services: [EPD_SERVICE_UUID] },
          { namePrefix: 'Lenmory' }
        ],
        optionalServices: [NRF_EPD_SERVICE_UUID, EPD_SERVICE_UUID]
      });
    } catch (e) {
      console.error(e);
      if (e.message) addLog("requestDevice: " + e.message);
      addLog("请检查蓝牙是否已开启，且使用的浏览器支持蓝牙！建议使用以下浏览器：");
      addLog("• 电脑: Chrome/Edge");
      addLog("• Android: Chrome/Edge");
      addLog("• iOS: Bluefy 浏览器");
      return;
    }

    await bleDevice.addEventListener('gattserverdisconnected', disconnect);
    setTimeout(async function () { await connect(); }, 300);
  }
}

async function reConnect() {
  if (reconnectActive) return;
  reconnectActive = true;
  updateButtonStatus(true);
  try {
    if (bleDevice == null && navigator.bluetooth && typeof navigator.bluetooth.getDevices === 'function') {
      const devices = await navigator.bluetooth.getDevices();
      bleDevice = devices.find(device => device && (device.name || '').startsWith('Lenmory')) || null;
    }

    if (bleDevice == null) {
      addLog('没有可重连的已授权设备，重新选择设备。');
      updateButtonStatus();
      await preConnect();
      return;
    }

    const device = bleDevice;
    device.removeEventListener('gattserverdisconnected', disconnect);
    if (device.gatt.connected) {
      const disconnected = new Promise(resolve =>
        device.addEventListener('gattserverdisconnected', resolve, { once: true }));
      device.gatt.disconnect();
      await Promise.race([disconnected, sleep(1000)]);
    }

    for (let attempt = 1; attempt <= RECONNECT_MAX_ATTEMPTS; attempt++) {
      resetVariables({ clearLog: false });
      bleDevice = device;
      device.removeEventListener('gattserverdisconnected', disconnect);
      device.addEventListener('gattserverdisconnected', disconnect);
      addLog(attempt === 1 ? '正在重连' : `正在重连 (${attempt}/${RECONNECT_MAX_ATTEMPTS})`);
      if (await connect()) return;

      if (attempt < RECONNECT_MAX_ATTEMPTS) {
        if (device.gatt.connected) device.gatt.disconnect();
        addLog('GATT 服务发现未完成，正在自动重试。');
        await sleep(RECONNECT_RETRY_DELAY_MS * attempt);
      }
    }
    addLog('自动重连失败，请确认设备仍在广播后重试。');
  } catch (e) {
    console.error(e);
    if (e.message) addLog('reconnect: ' + e.message);
  } finally {
    reconnectActive = false;
    updateButtonStatus();
  }
}

function handleDisplayError(code) {
  if (code === 'operation_busy' && deviceInitPending) {
    setStatus('屏幕正在完成上电刷新，连接初始化将自动重试。');
    scheduleDeviceInitRetry();
    return;
  }

  const busyTimeout = code === 'busy_timeout';
  const message = busyTimeout
    ? '屏幕 BUSY 等待超时，当前驱动可能与屏幕不匹配。请切换对应屏幕驱动后重试，蓝牙连接将保持。'
    : '设备正在执行其他显示操作，请稍后重试。';

  displayErrorActive = busyTimeout;
  cancelImagePrepareWait();
  cancelImageRefreshWait();
  imageTransferActive = false;
  if (slotActionPending) setSlotActionPending(false);
  if (slotReadState) failSlotImageRead(message);
  const status = document.getElementById('status');
  status.parentElement.style.display = 'block';
  setStatus(message);
  addLog(message, '', 'error');
  updateButtonStatus();
}

function clearDeviceInitRetry() {
  if (deviceInitRetryTimer != null) clearTimeout(deviceInitRetryTimer);
  deviceInitRetryTimer = null;
  deviceInitPending = false;
}

function scheduleDeviceInitRetry() {
  if (!deviceInitPending || !isBleConnected() || deviceInitRetryTimer != null) return;
  deviceInitRetryTimer = setTimeout(async () => {
    deviceInitRetryTimer = null;
    if (deviceInitPending && isBleConnected()) await write(EpdCmd.INIT);
  }, DEVICE_INIT_RETRY_DELAY_MS);
}

function handleNotify(value, idx) {
  const data = new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
  const isImageInfo = data.length >= 4 && data[0] === 0x69 && data[1] === 0x6D &&
    data[2] === 0x67 && data[3] === 0x3D;
  if (slotReadState && slotReadState.expectedChunk && !isImageInfo) {
    receiveSlotChunk(data);
    return;
  }

  const isTextNotification = data.length > 0 && data.every(byte => byte >= 0x20 && byte <= 0x7E);
  if (!isTextNotification && (data.length === EPD_CONFIG_SIZE || LEGACY_EPD_CONFIG_SIZES.includes(data.length))) {
    clearDeviceInitRetry();
    addLog(`收到配置：${bytes2hex(data)}`);
    const epdpins = document.getElementById("epdpins");
    const epddriver = document.getElementById("epddriver");
    epdpins.value = bytes2hex(data.slice(0, 7));
    if (data.length > 10) epdpins.value += bytes2hex(data.slice(10, 11));
    currentPinsValue = epdpins.value.trim().toLowerCase();
    epddriver.value = bytes2hex(data.slice(7, 8));
    const ledFlags = data.length > 14 ? data[14] : 1;
    const ledEnabled = (ledFlags & 0x01) !== 0;
    const ledChase = data[15] === 2 && (ledFlags & 0x02) === 0;
    const ledBrightnessLevel = ledFlags >> 2;
    document.getElementById('ledEnabled').checked = ledEnabled;
    document.getElementById('ledTransferChase').checked = ledChase;
    const persistedBrightness = data.length > 15 && data[15] === 2 && ledBrightnessLevel !== 0
      ? Math.round(ledBrightnessLevel * 100 / 63)
      : 2;
    setLedBrightness(persistedBrightness, false);
    if (data.length === EPD_CONFIG_SIZE) {
      setLedRgb(data[16], data[17], data[18], false);
    } else if (data.length > 9 && data[9] >= 16 && data[9] <= 18) {
      setLedRgb(data[9] === 16 ? 255 : 0, data[9] === 17 ? 255 : 0, data[9] === 18 ? 255 : 0, false);
    }
    addLog(ledEnabled ? 'LED ON' : 'LED OFF');
    displayErrorActive = false;
    updateDitcherOptions({ reloadImage: false });
  } else {
    if (textDecoder == null) textDecoder = new TextDecoder();
    const msg = textDecoder.decode(data);
    if (!msg.startsWith('chunk=')) addLog(msg, '⇓');
    if (applySlotsMessage(msg)) {
      addLog('图片槽位状态已更新。');
    } else if (msg === 'ready=1') {
      if (!completeImagePrepare()) completeImageRefresh();
    } else if (beginSlotImageRead(msg)) {
      addLog('开始接收槽位图片。');
    } else if (beginSlotChunk(msg)) {
      // The next notification contains the binary chunk.
    } else if (msg.startsWith('display_error=')) {
      handleDisplayError(msg.substring('display_error='.length));
    } else if (msg.startsWith('slot_error=')) {
      const errorMessage = `槽位操作失败：${msg.substring('slot_error='.length)}`;
      if (slotActionPending) setSlotActionPending(false);
      if (slotReadState) {
        failSlotImageRead(errorMessage);
      } else {
        const status = document.getElementById('slotReadStatus');
        status.hidden = false;
        status.textContent = errorMessage;
        addLog(errorMessage);
      }
    } else if (msg.startsWith('font=') || msg.startsWith('font_error=')) {
      // The picture-only host intentionally ignores the removed clock module.
    } else if (msg.startsWith('mtu=') && msg.length > 4) {
      const mtuParts = msg.substring(4).trim().split(/\s+/);
      const mtuSize = parseInt(mtuParts[0], 10);
      rleSupport = mtuParts.includes('rle=1');
      slotStreamSupport = mtuParts.includes('slot_stream=1');
      document.getElementById('mtusize').value = mtuSize;
      addLog(`MTU 已更新为: ${mtuSize}`);
      if (rleSupport) addLog('设备已启用 RLE 压缩传输。');
    } else if (msg.startsWith('t=') && msg.length > 2) {
      const t = parseInt(msg.substring(2)) + new Date().getTimezoneOffset() * 60;
      addLog(`远端时间: ${new Date(t * 1000).toLocaleString()}`);
      addLog(`本地时间: ${new Date().toLocaleString()}`);
    }
  }
}

async function connect() {
  if (bleDevice == null || nrfEpdCharacteristic != null || epdCharacteristic != null) return false;

  try {
    addLog("正在连接: " + bleDevice.name);
    gattServer = await bleDevice.gatt.connect();
    addLog('  找到 GATT Server');

    try {
      nrfEpdService = await gattServer.getPrimaryService(NRF_EPD_SERVICE_UUID);
      nrfEpdCharacteristic = await nrfEpdService.getCharacteristic(NRF_EPD_CHARACTERISTIC_UUID);
      try {
        nrfEpdVersionCharacteristic = await nrfEpdService.getCharacteristic(NRF_EPD_VERSION_UUID);
      } catch (_) {
        nrfEpdVersionCharacteristic = null;
      }
      addLog('  找到 6275 nRF 原生传图服务');
    } catch (nativeError) {
      nrfEpdService = null;
      nrfEpdCharacteristic = null;
      nrfEpdVersionCharacteristic = null;
      addLog('  当前固件未提供 6275 原生服务，尝试 FFFF 兼容通道');
    }

    try {
      legacyEpdService = await gattServer.getPrimaryService(EPD_SERVICE_UUID);
      legacyEpdCharacteristic = await legacyEpdService.getCharacteristic(EPD_WRITE_UUID);
      legacyEpdNotifyCharacteristic = await legacyEpdService.getCharacteristic(EPD_NOTIFY_UUID);
      addLog('  找到 FFFF 官方 App 兼容服务');
    } catch (legacyError) {
      legacyEpdService = null;
      legacyEpdCharacteristic = null;
      legacyEpdNotifyCharacteristic = null;
      if (!nrfEpdCharacteristic) throw legacyError;
      addLog('  未找到 FFFF 兼容服务，继续使用 nRF 原生服务');
    }

    if (!nrfEpdCharacteristic && !legacyEpdCharacteristic)
      throw new Error('设备未提供可用的 EPD 蓝牙服务');
    epdService = legacyEpdService || nrfEpdService;
    epdCharacteristic = legacyEpdCharacteristic || nrfEpdCharacteristic;
    epdNotifyCharacteristic = legacyEpdNotifyCharacteristic || nrfEpdCharacteristic;
  } catch (e) {
    console.error(e);
    if (e.message) addLog("connect: " + e.message);
    if (bleDevice && bleDevice.gatt && bleDevice.gatt.connected) bleDevice.gatt.disconnect();
    disconnect();
    return false;
  }

  try {
    if (nrfEpdCharacteristic) {
      nrfEpdCharacteristic.addEventListener('characteristicvaluechanged', handleNativeNrfNotification);
      await nrfEpdCharacteristic.startNotifications();
      addLog('  已启用 nRF 原生通知');
    }
    if (legacyEpdNotifyCharacteristic) {
      tgzRx = new MemobusClient.BlufiReassembler();
      tgzTxSequence = 0;
      tgzNoResponseRemaining = TGZ_WRITE_RESPONSE_INTERVAL;
      legacyEpdNotifyCharacteristic.addEventListener('characteristicvaluechanged', handleTgzNotification);
      await legacyEpdNotifyCharacteristic.startNotifications();
      addLog('  已启用 FFFF 兼容通知');
    }
  } catch (e) {
    console.error(e);
    if (e.message) addLog("startNotifications: " + e.message);
    if (bleDevice.gatt.connected) bleDevice.gatt.disconnect();
    finishDisconnect('通知启用失败。');
    return false;
  }

  try {
    if (nrfEpdCharacteristic) {
      if (nrfEpdVersionCharacteristic) {
        try {
          firmwareVersion = parseFirmwareVersion(await nrfEpdVersionCharacteristic.readValue());
          addLog(`固件版本: ${firmwareVersion.label}`);
        } catch (_) {
          addLog('固件版本特征暂不可读，继续初始化。');
        }
      }
      const panelMessage = waitForNativeNrfMessage(
        message => /(?:^|\s)panel=\d+/.test(message),
        15000,
        'nRF 屏幕识别'
      );
      await writeNativeNrfPayload(new Uint8Array([EpdCmd.INIT]), false);
      applyNativePanelMessage(await panelMessage);
      await refreshSlots(0);
      addLog('已启用 nRF 原生快速传图与图片槽功能。');
    } else {
      const handshake = await requestTgz(0x01, 0x05, null, 10000, '设备握手');
      applyTgzHandshake(handshake);
      await identifyTgzPanel();
      await refreshTgzStorage();
    }
  } catch (initError) {
    addLog(`设备初始化失败：${initError.message || initError}`);
    if (bleDevice.gatt.connected) bleDevice.gatt.disconnect();
    finishDisconnect('连接初始化失败。');
    return false;
  }

  document.getElementById("connectbutton").innerHTML = '断开';
  setStatus('设备已连接，可以离线传图。');
  updateButtonStatus();
  return true;
}

function setStatus(statusText) {
  document.getElementById("status").innerHTML = statusText;
}

function addLog(logTXT, action = '', type = '') {
  const log = document.getElementById("log");
  const now = new Date();
  const time = String(now.getHours()).padStart(2, '0') + ":" +
    String(now.getMinutes()).padStart(2, '0') + ":" +
    String(now.getSeconds()).padStart(2, '0') + " ";

  const logEntry = document.createElement('div');
  const timeSpan = document.createElement('span');
  logEntry.className = type ? 'log-line ' + type : 'log-line';
  timeSpan.className = 'time';
  timeSpan.textContent = time;
  logEntry.appendChild(timeSpan);

  if (action !== '') {
    const actionSpan = document.createElement('span');
    actionSpan.className = 'action';
    actionSpan.innerHTML = action;
    logEntry.appendChild(actionSpan);
  }
  logEntry.appendChild(document.createTextNode(logTXT));

  log.appendChild(logEntry);
  log.scrollTop = log.scrollHeight;

  while (log.childNodes.length > 20) {
    log.removeChild(log.firstChild);
  }
}

function clearLog() {
  document.getElementById("log").innerHTML = '';
}

function fillCanvas(style) {
  resetDitherPreviewSource();
  ctx.fillStyle = style;
  ctx.fillRect(0, 0, canvas.width, canvas.height);
  if (paintManager && paintManager.setBaseImageData) paintManager.setBaseImageData();
}

function cloneImageData(imageData) {
  return new ImageData(
    new Uint8ClampedArray(imageData.data),
    imageData.width,
    imageData.height
  );
}

function resetDitherPreviewSource() {
  ditherSourceImageData = null;
  ditherPreviewActive = false;
}

function setCanvasTitle(title) {
  const canvasTitle = document.querySelector('.canvas-title');
  if (canvasTitle) {
    canvasTitle.innerText = title;
    canvasTitle.style.display = title && title !== '' ? 'block' : 'none';
  }
}

function renderTransformedImagePreview(sourceImageData, commitHistory = false) {
  ditherSourceImageData = cloneImageData(sourceImageData);
  ditherPreviewActive = true;
  const settings = getDitherSettings();
  const processedData = processCanvasImageData();
  const finalImageData = decodeProcessedData(processedData, canvas.width, canvas.height, settings.mode);
  ctx.putImageData(finalImageData, 0, 0);

  if (paintManager && paintManager.setBaseImageData) paintManager.setBaseImageData();
  if (commitHistory && paintManager) {
    paintManager.clearHistory();
    paintManager.saveToHistory();
  }
}

function resetPaintForImageLoad() {
  if (!paintManager) return;
  paintManager.setActiveTool(null, '');
  paintManager.clearElements();
  paintManager.clearHistory();
}

function updateImage(file = null) {
  const imageFile = document.getElementById('imageFile');
  const selectedFile = file || (imageFile.files.length > 0 ? imageFile.files[0] : null);
  if (!selectedFile) {
    if (cropManager) cropManager.clearImage();
    fillCanvas('white');
    return;
  }

  resetDitherPreviewSource();
  resetPaintForImageLoad();
  cropManager.loadFile(selectedFile).catch((error) => {
    cropManager.clearImage();
    fillCanvas('white');
    addLog(`图片读取失败：${error.message || error}`);
    alert('图片文件无法读取，请重新选择。');
  });
}

function updateCanvasSize(options = {}) {
  const selectedSizeName = document.getElementById('canvasSize').value;
  const selectedSize = canvasSizes.find(size => size.name === selectedSizeName);
  const sizeChanged = canvas.width !== selectedSize.width || canvas.height !== selectedSize.height;

  if (!sizeChanged && options.reloadImage === false) {
    return;
  }

  resetDitherPreviewSource();
  canvas.width = selectedSize.width;
  canvas.height = selectedSize.height;

  if (options.reloadImage !== false) updateImage();
}

function prepareTgzTransferPreview() {
  const preview = document.getElementById('tgzTransferPreview');
  const previewContext = preview.getContext('2d');
  previewContext.fillStyle = '#f1f1f1';
  previewContext.fillRect(0, 0, preview.width, preview.height);
  if (canvas) previewContext.drawImage(canvas, 0, 0, preview.width, preview.height);
  preview.style.clipPath = 'inset(0 0 100% 0)';
}

function showTgzTransferOverlay() {
  const overlay = document.getElementById('tgzTransferOverlay');
  prepareTgzTransferPreview();
  overlay.hidden = false;
  updateTgzTransferOverlay(0);
}

function updateTgzTransferOverlay(progress) {
  tgzTransferTargetProgress = Math.max(0, Math.min(100, Number(progress) || 0));
  if (tgzTransferProgressFrame != null) return;
  tgzTransferProgressFrame = requestAnimationFrame(() => {
    const normalized = tgzTransferTargetProgress;
    const visiblePercent = Math.floor(normalized);
    document.getElementById('tgzTransferPreview').style.clipPath =
      `inset(0 0 ${100 - normalized}% 0)`;
    document.getElementById('tgzTransferTitle').textContent = normalized < 100
      ? `正在传输 ${visiblePercent}%`
      : '传输完成，屏幕刷新中';
    document.getElementById('tgzTransferBar').style.width = `${normalized}%`;
    tgzTransferProgressFrame = null;
  });
}

function hideTgzTransferOverlay() {
  if (tgzTransferProgressFrame != null) cancelAnimationFrame(tgzTransferProgressFrame);
  tgzTransferProgressFrame = null;
  tgzTransferTargetProgress = 0;
  document.getElementById('tgzTransferOverlay').hidden = true;
}

function configureTgzUi() {
  const driverSelect = document.getElementById('epddriver');
  driverSelect.innerHTML = [
    '<option value="0" data-color="fourColor" data-size="TGZ_760_528">自动识别</option>',
    '<option value="1" data-color="fourColor" data-size="TGZ_760_528">SE0398 A0</option>',
    '<option value="2" data-color="fourColor" data-size="TGZ_760_528">SE0398 New-A1</option>',
    '<option value="3" data-color="sixColor" data-size="TGZ_760_528">3.65 英寸六色 E6</option>',
    '<option value="4" data-color="sixColor" data-size="TGZ_760_528">3.98 英寸六色 E6</option>',
    '<option value="5" data-color="sixColor" data-size="TGZ_760_528">3.68 英寸六色 E6</option>',
  ].join('');
  driverSelect.value = '0';
  driverSelect.closest('.flex-group').classList.remove('debug');
  const pins = document.getElementById('epdpins');
  pins.hidden = true;
  if (pins.previousElementSibling) pins.previousElementSibling.hidden = true;
  document.getElementById('setDriverbutton').textContent = '切换';
  document.getElementById('canvasSize').value = 'TGZ_760_528';
  document.getElementById('slotRefreshAfterSave').addEventListener('change', async event => {
    if (!isBleConnected()) return;
    try {
      if (nrfEpdCharacteristic) {
        if (event.target.checked && !tgzStorageAvailable)
          throw new Error('未识别到可用外置 Flash');
        if (!event.target.checked)
          await prepareNativeNrfTransfer(false, 0xFFFFFFFF, false);
      } else {
        await setTgzTransferMode(event.target.checked);
      }
      addLog(event.target.checked ? '传图模式：保存到外置 Flash' : '传图模式：直接显示');
    } catch (error) {
      event.target.checked = false;
      addLog(error.message || String(error));
    }
  });
}

function updateDitcherOptions(options = {}) {
  const epdDriverSelect = document.getElementById('epddriver');
  const selectedOption = epdDriverSelect.options[epdDriverSelect.selectedIndex];
  const colorMode = selectedOption.getAttribute('data-color');
  const canvasSize = selectedOption.getAttribute('data-size');

  updateDriverMeta(selectedOption);
  if (colorMode) document.getElementById('ditherMode').value = colorMode;
  if (canvasSize) document.getElementById('canvasSize').value = canvasSize;

  updateCanvasSize(options);
  if (paintManager && typeof paintManager.refreshMatterTemplatePalette === 'function') {
    paintManager.refreshMatterTemplatePalette();
  }
}

function updateDriverMeta(option) {
  const meta = document.getElementById('driverMeta');
  if (!meta) return;

  const epdDriverSelect = document.getElementById('epddriver');
  const selectedOption = option || epdDriverSelect.options[epdDriverSelect.selectedIndex];
  const driverName = selectedOption ? selectedOption.textContent.trim() : 'EPD';
  meta.textContent = `${driverName} · Web Bluetooth`;
}

function clearCanvas() {
  if (confirm('清除画布内容?')) {
    if (cropManager) cropManager.clearImage();
    const imageFile = document.getElementById('imageFile');
    if (imageFile) imageFile.value = '';
    fillCanvas('white');
    paintManager.clearElements(); // Clear stored text positions and line segments
    if (paintManager.setBaseImageData) paintManager.setBaseImageData();
    if (paintManager.clearScheduleCache) paintManager.clearScheduleCache();
    paintManager.clearHistory();
    paintManager.saveToHistory(); // Save cleared canvas to history
    return true;
  }
  return false;
}

function getDitherSettings() {
  return {
    contrast: parseFloat(document.getElementById('ditherContrast').value),
    brightness: parseFloat(document.getElementById('ditherBrightness').value),
    saturation: parseFloat(document.getElementById('ditherSaturation').value),
    alg: document.getElementById('ditherAlg').value,
    strength: parseFloat(document.getElementById('ditherStrength').value),
    mode: document.getElementById('ditherMode').value,
    filter: document.getElementById('tgzFilter')?.value || 'none'
  };
}

function prepareDitherImageData(sourceImageData) {
  return new ImageData(
    new Uint8ClampedArray(sourceImageData.data),
    sourceImageData.width,
    sourceImageData.height
  );
}

function processCanvasImageData() {
  const settings = getDitherSettings();
  if (!ditherPreviewActive || !ditherSourceImageData) {
    ditherSourceImageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
  }
  const sourceImageData = cloneImageData(ditherSourceImageData);
  const imageData = applyTgzFilter(prepareDitherImageData(sourceImageData), settings.filter);
  return processImageData(ditherImage(imageData, settings.alg, settings.strength, settings.mode, settings), settings.mode);
}

function convertDithering() {
  paintManager.redrawTextElements();
  paintManager.redrawLineSegments();
  if (paintManager.redrawTodoItems) paintManager.redrawTodoItems();
  if (paintManager.drawSchedule) paintManager.drawSchedule();

  const settings = getDitherSettings();
  const processedData = processCanvasImageData();
  const finalImageData = decodeProcessedData(processedData, canvas.width, canvas.height, settings.mode);
  ctx.putImageData(finalImageData, 0, 0);
  ditherPreviewActive = true;

  paintManager.saveToHistory(); // Save dithered image to history
}

function applyDither() {
  convertDithering();
}

function setDitherAdjustment(id, value, digits) {
  const input = document.getElementById(id);
  const label = document.getElementById(`${id}Value`);
  input.value = value;
  label.innerText = parseFloat(value).toFixed(digits);
  updateRangeFill(input);
}

function resetDitherAdjustments() {
  setDitherAdjustment('ditherStrength', 0.6, 1);
  setDitherAdjustment('ditherContrast', 1.4, 1);
  setDitherAdjustment('ditherBrightness', 0.9, 1);
  setDitherAdjustment('ditherSaturation', 1.1, 1);
  applyDither();
}

const CALENDAR_PREVIEW_COLORS = Object.freeze({
  white: '#ffffff',
  black: '#000000',
  red: '#d71920',
  yellow: '#f5d328'
});
const CALENDAR_FONT_DEFAULTS = Object.freeze({
  title: 28,
  mainDay: 170,
  weekday: 28,
  cellDay: 24,
  cellLunar: 13
});
const LUNAR_DAY_NAMES = [
  '', '初一', '初二', '初三', '初四', '初五', '初六', '初七', '初八', '初九', '初十',
  '十一', '十二', '十三', '十四', '十五', '十六', '十七', '十八', '十九', '二十',
  '廿一', '廿二', '廿三', '廿四', '廿五', '廿六', '廿七', '廿八', '廿九', '三十'
];
const ZODIAC_NAMES = ['鼠', '牛', '虎', '兔', '龙', '蛇', '马', '羊', '猴', '鸡', '狗', '猪'];

function getCalendarStyleElements() {
  return {
    panel: document.getElementById('calendarStylePanel'),
    toggle: document.getElementById('calendarstylebutton'),
    preview: document.getElementById('calendarStylePreview'),
    layout: document.getElementById('calendarStyleLayout'),
    fontPreset: document.getElementById('calendarStyleFontPreset'),
    font: document.getElementById('calendarStyleFont'),
    textRender: document.getElementById('calendarStyleTextRender'),
    title: document.getElementById('calendarStyleTitle'),
    accent: document.getElementById('calendarStyleAccent'),
    lunar: document.getElementById('calendarStyleLunar'),
    fontFile: document.getElementById('calendarStyleFontFile'),
    render: document.getElementById('calendarStyleRender'),
    send: document.getElementById('calendarStyleSend'),
    reset: document.getElementById('calendarFontReset'),
    sizes: {
      title: document.getElementById('calendarFontTitle'),
      mainDay: document.getElementById('calendarFontMainDay'),
      weekday: document.getElementById('calendarFontWeekday'),
      cellDay: document.getElementById('calendarFontCellDay'),
      cellLunar: document.getElementById('calendarFontCellLunar')
    }
  };
}

function getCalendarStyleProfile() {
  const mode = document.getElementById('ditherMode')?.value || 'fourColor';
  return {
    width: canvas?.width || 768,
    height: canvas?.height || 552,
    numericColorMode: mode === 'sevenColor' ? 7 : (mode === 'fourColor' ? 4 : (mode === 'threeColor' ? 3 : 2))
  };
}

function getCalendarPreviewColors(profile) {
  if (profile.numericColorMode >= 4) return CALENDAR_PREVIEW_COLORS;
  if (profile.numericColorMode === 3) return { ...CALENDAR_PREVIEW_COLORS, yellow: CALENDAR_PREVIEW_COLORS.white };
  return { ...CALENDAR_PREVIEW_COLORS, red: CALENDAR_PREVIEW_COLORS.black, yellow: CALENDAR_PREVIEW_COLORS.white };
}

function getLunarInfo(date) {
  try {
    const parts = new Intl.DateTimeFormat('zh-CN-u-ca-chinese', {
      year: 'numeric', month: 'long', day: 'numeric'
    }).formatToParts(date);
    const valueOf = (type) => parts.find((part) => part.type === type)?.value || '';
    const dayNumber = parseInt(valueOf('day'), 10) || 1;
    const relatedYear = parseInt(valueOf('relatedYear'), 10) || date.getFullYear();
    const month = valueOf('month');
    const day = LUNAR_DAY_NAMES[dayNumber] || String(dayNumber);
    const zodiac = ZODIAC_NAMES[((relatedYear - 4) % 12 + 12) % 12];
    return {
      month,
      day,
      dayNumber,
      dateText: `${month}${day}`,
      yearText: `${valueOf('yearName')}${zodiac}年`
    };
  } catch (_) {
    return { month: '', day: '', dayNumber: 0, dateText: '', yearText: '' };
  }
}

function getNextSolarTerm(date) {
  const terms = [
    [0, 5, '小寒'], [0, 20, '大寒'], [1, 4, '立春'], [1, 19, '雨水'], [2, 5, '惊蛰'], [2, 20, '春分'],
    [3, 4, '清明'], [3, 20, '谷雨'], [4, 5, '立夏'], [4, 21, '小满'], [5, 5, '芒种'], [5, 21, '夏至'],
    [6, 7, '小暑'], [6, 23, '大暑'], [7, 7, '立秋'], [7, 23, '处暑'], [8, 7, '白露'], [8, 23, '秋分'],
    [9, 8, '寒露'], [9, 23, '霜降'], [10, 7, '立冬'], [10, 22, '小雪'], [11, 7, '大雪'], [11, 21, '冬至']
  ];
  const today = new Date(date.getFullYear(), date.getMonth(), date.getDate());
  for (const [month, day, name] of terms) {
    const target = new Date(date.getFullYear(), month, day);
    if (target >= today) return { name, days: Math.round((target - today) / 86400000) };
  }
  const target = new Date(date.getFullYear() + 1, terms[0][0], terms[0][1]);
  return { name: terms[0][2], days: Math.round((target - today) / 86400000) };
}

function getIsoWeek(date) {
  const target = new Date(Date.UTC(date.getFullYear(), date.getMonth(), date.getDate()));
  const day = target.getUTCDay() || 7;
  target.setUTCDate(target.getUTCDate() + 4 - day);
  const yearStart = new Date(Date.UTC(target.getUTCFullYear(), 0, 1));
  return Math.ceil((((target - yearStart) / 86400000) + 1) / 7);
}

function getCalendarCellLabel(date) {
  const festivals = {
    '1-1': '元旦', '2-14': '情人节', '3-8': '妇女节', '5-1': '劳动节', '6-1': '儿童节',
    '10-1': '国庆节', '12-25': '圣诞节'
  };
  const festival = festivals[`${date.getMonth() + 1}-${date.getDate()}`];
  if (festival) return { text: festival, festival: true };
  const lunar = getLunarInfo(date);
  return { text: lunar.dayNumber === 1 ? lunar.month : lunar.day, festival: false };
}

function calendarRoundRect(context, x, y, width, height, radius) {
  const r = Math.max(0, Math.min(radius, width / 2, height / 2));
  context.beginPath();
  context.moveTo(x + r, y);
  context.lineTo(x + width - r, y);
  context.quadraticCurveTo(x + width, y, x + width, y + r);
  context.lineTo(x + width, y + height - r);
  context.quadraticCurveTo(x + width, y + height, x + width - r, y + height);
  context.lineTo(x + r, y + height);
  context.quadraticCurveTo(x, y + height, x, y + height - r);
  context.lineTo(x, y + r);
  context.quadraticCurveTo(x, y, x + r, y);
  context.closePath();
}

function getCalendarStyleSettings() {
  const elements = getCalendarStyleElements();
  const sizes = {};
  Object.entries(elements.sizes).forEach(([role, input]) => {
    const value = Number(input?.value);
    sizes[role] = Number.isFinite(value) ? value : CALENDAR_FONT_DEFAULTS[role];
  });
  return {
    layout: elements.layout?.value || 'grid',
    fontFamily: customCalendarFontFamily || elements.font?.value || 'Microsoft YaHei, SimHei, sans-serif',
    textRender: elements.textRender?.value || 'smooth',
    title: (elements.title?.value || '').trim(),
    accent: elements.accent?.value || 'red',
    showLunar: elements.lunar?.checked !== false,
    sizes
  };
}

function calendarStyleScale(profile) {
  return Math.max(0.42, Math.min(profile.width / 768, profile.height / 552));
}

function calendarFontSize(settings, role, profile, multiplier = 1) {
  return Math.max(7, Math.round((settings.sizes[role] || CALENDAR_FONT_DEFAULTS[role]) * calendarStyleScale(profile) * multiplier));
}

function drawCalendarText(context, text, x, y, options = {}) {
  const value = String(text ?? '');
  if (!value) return;
  const settings = getCalendarStyleSettings();
  const size = options.size || 24;
  const weight = options.weight || 600;
  context.save();
  context.fillStyle = options.color || CALENDAR_PREVIEW_COLORS.black;
  context.strokeStyle = options.strokeColor || context.fillStyle;
  context.lineWidth = options.lineWidth || Math.max(1, Math.round(size / 22));
  context.font = `${weight} ${size}px ${settings.fontFamily}`;
  context.textAlign = options.align || 'left';
  context.textBaseline = options.baseline || 'alphabetic';
  if (settings.textRender === 'crisp') {
    context.imageSmoothingEnabled = false;
    if ('fontKerning' in context) context.fontKerning = 'none';
    context.fillText(value, Math.round(x), Math.round(y));
  } else if (settings.textRender === 'outline') {
    context.strokeText(value, Math.round(x), Math.round(y));
    context.fillText(value, Math.round(x), Math.round(y));
  } else if (settings.textRender === 'pixelated' || settings.textRender === 'bold-pixel') {
    const metrics = context.measureText(value);
    const padding = Math.max(4, Math.ceil(size * 0.18));
    const source = document.createElement('canvas');
    source.width = Math.max(1, Math.ceil(metrics.width + padding * 2));
    source.height = Math.max(1, Math.ceil(size * 1.45 + padding * 2));
    const sourceContext = source.getContext('2d');
    sourceContext.fillStyle = context.fillStyle;
    sourceContext.strokeStyle = context.strokeStyle;
    sourceContext.lineWidth = settings.textRender === 'bold-pixel' ? Math.max(1, Math.round(size / 18)) : 1;
    sourceContext.font = context.font;
    sourceContext.textBaseline = 'alphabetic';
    const baseline = padding + size;
    if (settings.textRender === 'bold-pixel') sourceContext.strokeText(value, padding, baseline);
    sourceContext.fillText(value, padding, baseline);
    const low = document.createElement('canvas');
    const pixelScale = settings.textRender === 'bold-pixel' ? 0.42 : 0.5;
    low.width = Math.max(1, Math.round(source.width * pixelScale));
    low.height = Math.max(1, Math.round(source.height * pixelScale));
    const lowContext = low.getContext('2d');
    lowContext.imageSmoothingEnabled = true;
    lowContext.drawImage(source, 0, 0, low.width, low.height);
    let destX = x - padding;
    if (context.textAlign === 'center') destX = x - source.width / 2;
    else if (context.textAlign === 'right') destX = x - source.width + padding;
    let destY = y - baseline;
    if (context.textBaseline === 'middle') destY = y - source.height / 2;
    else if (context.textBaseline === 'top') destY = y;
    context.imageSmoothingEnabled = false;
    context.drawImage(low, Math.round(destX), Math.round(destY), source.width, source.height);
  } else {
    context.fillText(value, x, y);
  }
  context.restore();
}

function getCalendarWeekdays(weekStart) {
  const names = ['日', '一', '二', '三', '四', '五', '六'];
  return Array.from({ length: 7 }, (_, index) => {
    const day = (weekStart + index) % 7;
    return { day, text: names[day], weekend: day === 0 || day === 6 };
  });
}

function getCalendarAccent(profile, settings, colors) {
  if (settings.accent === 'yellow') return profile.numericColorMode >= 4 ? colors.yellow : colors.black;
  if (settings.accent === 'black') return colors.black;
  return colors.red;
}

function drawCalendarMonthGrid(context, date, profile, settings, bounds, options = {}) {
  const colors = getCalendarPreviewColors(profile);
  const accent = getCalendarAccent(profile, settings, colors);
  const softAccent = profile.numericColorMode >= 4 ? colors.yellow : colors.white;
  const weekStart = Number(document.getElementById('weekStart')?.value) || 0;
  const year = date.getFullYear();
  const month = date.getMonth();
  const firstOffset = (new Date(year, month, 1).getDay() - weekStart + 7) % 7;
  const daysInMonth = new Date(year, month + 1, 0).getDate();
  const rows = Math.ceil((firstOffset + daysInMonth) / 7);
  const weekHeight = Math.max(22, Math.floor(bounds.height * 0.12));
  const gridTop = bounds.y + weekHeight + 5;
  const cellWidth = bounds.width / 7;
  const cellHeight = Math.max(18, Math.floor((bounds.height - weekHeight - 5) / rows));
  const numberSize = calendarFontSize(settings, 'cellDay', profile);
  const labelSize = calendarFontSize(settings, 'cellLunar', profile);

  getCalendarWeekdays(weekStart).forEach((weekday, index) => {
    const x = bounds.x + index * cellWidth;
    context.fillStyle = weekday.weekend ? accent : softAccent;
    if (options.squareHeader) context.fillRect(x + 1, bounds.y, cellWidth - 2, weekHeight);
    else {
      calendarRoundRect(context, x + 2, bounds.y, cellWidth - 4, weekHeight, Math.min(8, weekHeight / 3));
      context.fill();
    }
    drawCalendarText(context, weekday.text, x + cellWidth / 2, bounds.y + weekHeight * 0.7, {
      size: Math.max(10, Math.round(calendarFontSize(settings, 'weekday', profile) * 0.7)),
      weight: 800,
      color: weekday.weekend ? colors.white : accent,
      align: 'center'
    });
  });

  context.strokeStyle = colors.black;
  context.lineWidth = options.lineWidth || 2;
  for (let row = 0; row <= rows; row++) {
    const y = Math.round(gridTop + row * cellHeight);
    context.beginPath();
    context.moveTo(bounds.x, y);
    context.lineTo(bounds.x + bounds.width, y);
    context.stroke();
  }
  for (let col = 0; col <= 7; col++) {
    const x = bounds.x + col * cellWidth;
    context.beginPath();
    context.moveTo(x, gridTop);
    context.lineTo(x, gridTop + rows * cellHeight);
    context.stroke();
  }

  for (let day = 1; day <= daysInMonth; day++) {
    const position = firstOffset + day - 1;
    const col = position % 7;
    const row = Math.floor(position / 7);
    const x = bounds.x + col * cellWidth;
    const y = gridTop + row * cellHeight;
    const actualWeekday = new Date(year, month, day).getDay();
    const isToday = day === date.getDate();
    if (isToday) {
      context.fillStyle = softAccent;
      calendarRoundRect(context, x + 5, y + 4, Math.max(8, cellWidth - 10), Math.max(8, cellHeight - 8), Math.min(9, cellHeight / 5));
      context.fill();
      context.strokeStyle = accent;
      context.lineWidth = 2;
      context.stroke();
    }
    const textX = x + cellWidth / 2;
    const numberY = y + Math.min(cellHeight * 0.48, numberSize + 7);
    drawCalendarText(context, day, textX, numberY, {
      size: numberSize,
      weight: isToday ? 900 : 800,
      color: isToday || actualWeekday === 0 || actualWeekday === 6 ? accent : colors.black,
      align: 'center'
    });
    if (settings.showLunar) {
      const label = getCalendarCellLabel(new Date(year, month, day));
      drawCalendarText(context, label.text, textX, Math.min(y + cellHeight - 5, numberY + labelSize + 3), {
        size: labelSize,
        weight: 700,
        color: label.festival ? accent : colors.black,
        align: 'center'
      });
    }
  }
}

function drawFramedCalendarGrid(context, date, profile, settings, bounds, options = {}) {
  const colors = getCalendarPreviewColors(profile);
  const accent = getCalendarAccent(profile, settings, colors);
  const padding = options.padding || Math.max(7, Math.round(12 * calendarStyleScale(profile)));
  context.fillStyle = colors.white;
  calendarRoundRect(context, bounds.x, bounds.y, bounds.width, bounds.height, options.radius || 12);
  context.fill();
  context.strokeStyle = options.stroke || accent;
  context.lineWidth = options.strokeWidth || 2;
  context.stroke();
  drawCalendarMonthGrid(context, date, profile, settings, {
    x: bounds.x + padding,
    y: bounds.y + padding,
    width: bounds.width - padding * 2,
    height: bounds.height - padding * 2
  }, options);
}

function drawCalendarStyle(context, date, profile) {
  const settings = getCalendarStyleSettings();
  const colors = getCalendarPreviewColors(profile);
  const accent = getCalendarAccent(profile, settings, colors);
  const softAccent = profile.numericColorMode >= 4 ? colors.yellow : colors.white;
  const { width, height } = profile;
  const scale = calendarStyleScale(profile);
  const pad = Math.max(12, Math.round(width * 0.035));
  const monthText = `${date.getFullYear()}.${String(date.getMonth() + 1).padStart(2, '0')}`;
  const weekdayText = `星期${getCalendarWeekdays(0)[date.getDay()].text}`;
  const lunar = getLunarInfo(date);
  const solarTerm = getNextSolarTerm(date);
  const titleSize = calendarFontSize(settings, 'title', profile);
  const mainDaySize = calendarFontSize(settings, 'mainDay', profile);
  const weekdaySize = calendarFontSize(settings, 'weekday', profile);
  const monthSize = Math.max(15, Math.round(24 * scale));
  const lunarSize = Math.max(13, Math.round(22 * scale));
  const smallSize = Math.max(11, Math.round(18 * scale));
  context.fillStyle = colors.white;
  context.fillRect(0, 0, width, height);

  if (settings.layout === 'split') {
    const leftWidth = Math.round(width * 0.36);
    context.fillStyle = softAccent;
    context.fillRect(0, 0, leftWidth, height);
    context.fillStyle = accent;
    context.fillRect(leftWidth - Math.max(4, Math.round(6 * scale)), 0, Math.max(4, Math.round(6 * scale)), height);
    drawCalendarText(context, settings.title, pad, Math.round(48 * scale), { size: titleSize, weight: 850, color: colors.black });
    drawCalendarText(context, date.getDate(), leftWidth / 2, height * 0.48, { size: Math.round(mainDaySize * 0.82), weight: 950, color: accent, align: 'center' });
    drawCalendarText(context, weekdayText, leftWidth / 2, height * 0.62, { size: weekdaySize, weight: 800, color: colors.black, align: 'center' });
    if (settings.showLunar) drawCalendarText(context, lunar.dateText, leftWidth / 2, height * 0.71, { size: lunarSize, weight: 700, color: accent, align: 'center' });
    drawCalendarText(context, monthText, width - pad, Math.round(50 * scale), { size: monthSize, weight: 850, color: accent, align: 'right' });
    drawCalendarMonthGrid(context, date, profile, settings, { x: leftWidth + pad, y: Math.round(78 * scale), width: width - leftWidth - pad * 2, height: height - Math.round(100 * scale) });
    return;
  }

  if (settings.layout === 'dashboard') {
    const sideWidth = Math.round(width * 0.3);
    drawCalendarText(context, settings.title, pad, Math.round(42 * scale), { size: titleSize, weight: 850, color: colors.black });
    drawCalendarText(context, monthText, width - pad, Math.round(42 * scale), { size: monthSize, weight: 850, color: accent, align: 'right' });
    const cardY = Math.round(68 * scale);
    const cardHeight = Math.round(150 * scale);
    context.fillStyle = accent;
    calendarRoundRect(context, pad, cardY, sideWidth, cardHeight, Math.round(16 * scale));
    context.fill();
    drawCalendarText(context, date.getDate(), pad + sideWidth / 2, cardY + cardHeight * 0.69, { size: Math.round(mainDaySize * 0.5), weight: 950, color: colors.white, align: 'center' });
    drawCalendarText(context, weekdayText, pad + sideWidth / 2, cardY + cardHeight * 0.91, { size: Math.round(weekdaySize * 0.8), weight: 800, color: colors.white, align: 'center' });
    const info = [['农历', lunar.dateText || '--'], ['周数', `${getIsoWeek(date)}周`], ['节气', solarTerm.days === 0 ? solarTerm.name : `${solarTerm.name}-${solarTerm.days}`]];
    info.forEach((item, index) => {
      const y = cardY + cardHeight + Math.round((32 + index * 58) * scale);
      context.fillStyle = index % 2 === 0 ? softAccent : colors.white;
      calendarRoundRect(context, pad, y, sideWidth, Math.round(42 * scale), Math.round(10 * scale));
      context.fill();
      drawCalendarText(context, item[0], pad + Math.round(14 * scale), y + Math.round(27 * scale), { size: Math.round(smallSize * 0.9), weight: 700, color: colors.black });
      drawCalendarText(context, item[1], pad + sideWidth - Math.round(12 * scale), y + Math.round(27 * scale), { size: smallSize, weight: 850, color: accent, align: 'right' });
    });
    drawCalendarMonthGrid(context, date, profile, settings, { x: pad + sideWidth + Math.round(22 * scale), y: cardY, width: width - pad * 2 - sideWidth - Math.round(22 * scale), height: height - cardY - Math.round(24 * scale) }, { lineWidth: 2 });
    return;
  }

  if (settings.layout === 'classic') {
    const binderHeight = Math.round(72 * scale);
    context.fillStyle = accent;
    context.fillRect(0, 0, width, binderHeight);
    context.fillStyle = colors.black;
    for (let index = 0; index < 6; index++) {
      const x = pad + Math.round(38 * scale) + index * ((width - pad * 2 - Math.round(76 * scale)) / 5);
      context.beginPath();
      context.arc(x, Math.round(18 * scale), Math.max(3, Math.round(6 * scale)), 0, Math.PI * 2);
      context.fill();
    }
    drawCalendarText(context, settings.title, pad, Math.round(46 * scale), { size: titleSize, weight: 850, color: colors.white });
    drawCalendarText(context, `${date.getFullYear()} 年 ${date.getMonth() + 1} 月`, width - pad, Math.round(46 * scale), { size: monthSize, weight: 850, color: colors.white, align: 'right' });
    context.fillStyle = softAccent;
    context.fillRect(0, binderHeight, width, Math.max(6, Math.round(12 * scale)));
    drawFramedCalendarGrid(context, date, profile, settings, { x: pad, y: binderHeight + Math.round(24 * scale), width: width - pad * 2, height: height - binderHeight - Math.round(54 * scale) }, { squareHeader: true, lineWidth: 2, stroke: colors.black });
    return;
  }

  if (settings.layout === 'duo') {
    const leftWidth = Math.round(width * 0.34);
    context.fillStyle = softAccent;
    context.fillRect(0, 0, leftWidth, height);
    context.fillStyle = accent;
    context.fillRect(leftWidth - Math.max(5, Math.round(8 * scale)), 0, Math.max(5, Math.round(8 * scale)), height);
    drawCalendarText(context, monthText, leftWidth / 2, pad + Math.round(36 * scale), { size: monthSize, weight: 850, color: accent, align: 'center' });
    drawCalendarText(context, date.getDate(), leftWidth / 2, height * 0.52, { size: Math.round(mainDaySize * 0.72), weight: 950, color: colors.black, align: 'center' });
    drawCalendarText(context, weekdayText, leftWidth / 2, height * 0.66, { size: weekdaySize, weight: 850, color: accent, align: 'center' });
    if (settings.showLunar) drawCalendarText(context, lunar.dateText, leftWidth / 2, height * 0.76, { size: lunarSize, weight: 750, color: colors.black, align: 'center' });
    drawFramedCalendarGrid(context, date, profile, settings, { x: leftWidth + pad, y: pad, width: width - leftWidth - pad * 2, height: height - pad * 2 }, { stroke: colors.black });
    return;
  }

  const headerHeight = Math.max(Math.round(104 * scale), Math.round(height * 0.2));
  context.fillStyle = softAccent;
  calendarRoundRect(context, pad, pad, width - pad * 2, headerHeight, Math.round(22 * scale));
  context.fill();
  const dayWidth = Math.max(Math.round(98 * scale), Math.round(width * 0.18));
  context.fillStyle = accent;
  calendarRoundRect(context, pad + Math.round(14 * scale), pad + Math.round(14 * scale), dayWidth, headerHeight - Math.round(28 * scale), Math.round(16 * scale));
  context.fill();
  drawCalendarText(context, date.getDate(), pad + Math.round(width * 0.085), pad + headerHeight * 0.68, { size: Math.round(mainDaySize * 0.38), weight: 950, color: colors.white, align: 'center' });
  drawCalendarText(context, settings.title || monthText, pad + Math.round(width * 0.21), pad + headerHeight * 0.58, { size: titleSize, weight: 850, color: colors.black });
  drawFramedCalendarGrid(context, date, profile, settings, { x: pad, y: pad + headerHeight + Math.round(18 * scale), width: width - pad * 2, height: height - pad * 2 - headerHeight - Math.round(18 * scale) }, { stroke: colors.black, lineWidth: 2 });
}

function renderCalendarStylePreview() {
  const elements = getCalendarStyleElements();
  if (!elements.preview || !canvas) return false;
  const profile = getCalendarStyleProfile();
  if (elements.preview.width !== profile.width) elements.preview.width = profile.width;
  if (elements.preview.height !== profile.height) elements.preview.height = profile.height;
  elements.preview.style.aspectRatio = `${profile.width} / ${profile.height}`;
  drawCalendarStyle(elements.preview.getContext('2d'), new Date(), profile);
  return true;
}

function scheduleCalendarStylePreview() {
  const panel = document.getElementById('calendarStylePanel');
  if (!panel || panel.hidden) return;
  clearTimeout(calendarStyleRenderTimer);
  calendarStyleRenderTimer = setTimeout(renderCalendarStylePreview, 30);
}

function toggleCalendarStylePanel(forceOpen) {
  const elements = getCalendarStyleElements();
  if (!elements.panel) return;
  const open = typeof forceOpen === 'boolean' ? forceOpen : elements.panel.hidden;
  elements.panel.hidden = !open;
  elements.toggle?.setAttribute('aria-expanded', open ? 'true' : 'false');
  elements.toggle?.classList.toggle('primary', open);
  elements.toggle?.classList.toggle('secondary', !open);
  if (open) renderCalendarStylePreview();
}

async function applyCalendarStyleToImageCanvas(options = {}) {
  const elements = getCalendarStyleElements();
  if (!renderCalendarStylePreview()) return false;
  const previewContext = elements.preview.getContext('2d');
  const imageData = previewContext.getImageData(0, 0, elements.preview.width, elements.preview.height);
  if (cropManager) cropManager.clearImage();
  resetPaintForImageLoad();
  ditherSourceImageData = cloneImageData(imageData);
  ditherPreviewActive = true;
  calendarStyleImageActive = true;
  ctx.putImageData(imageData, 0, 0);
  if (paintManager?.setBaseImageData) paintManager.setBaseImageData();
  if (paintManager) {
    paintManager.clearHistory();
    paintManager.saveToHistory();
  }
  setCanvasTitle('日历风格');
  setStatus(options.forSend ? '日历图片已生成，准备发送。' : '日历图片已生成到图片预览。');
  addLog(options.forSend ? '日历图片已生成，开始发送。' : '日历图片已生成到图片预览。');
  document.getElementById('image-panel')?.scrollIntoView({ behavior: 'smooth', block: 'start' });
  if (options.forSend) return sendimg();
  return true;
}

function updateCalendarFontOutput(input) {
  const output = document.querySelector(`[data-size-value-for="${input.id}"]`);
  if (output) output.textContent = `${input.value}px`;
}

function resetCalendarFontSizes() {
  const elements = getCalendarStyleElements();
  Object.entries(elements.sizes).forEach(([role, input]) => {
    if (!input) return;
    input.value = CALENDAR_FONT_DEFAULTS[role];
    updateCalendarFontOutput(input);
    updateRangeFill(input);
  });
  renderCalendarStylePreview();
}

function initCalendarStyleControls() {
  const elements = getCalendarStyleElements();
  if (!elements.panel) return;
  const renderControls = [elements.layout, elements.textRender, elements.title, elements.accent, elements.lunar, ...Object.values(elements.sizes)];
  renderControls.forEach((control) => {
    if (!control) return;
    const eventName = control.type === 'checkbox' || control.tagName === 'SELECT' ? 'change' : 'input';
    control.addEventListener(eventName, () => {
      if (control.type === 'range') updateCalendarFontOutput(control);
      scheduleCalendarStylePreview();
    });
  });
  elements.fontPreset?.addEventListener('change', () => {
    if (elements.fontPreset.value !== 'custom') {
      customCalendarFontFamily = '';
      elements.font.value = elements.fontPreset.value;
    }
    renderCalendarStylePreview();
  });
  elements.font?.addEventListener('input', () => {
    customCalendarFontFamily = '';
    elements.fontPreset.value = 'custom';
    scheduleCalendarStylePreview();
  });
  elements.fontFile?.addEventListener('change', async () => {
    const file = elements.fontFile.files?.[0];
    if (!file) return;
    if (!('FontFace' in window)) {
      addLog('当前浏览器不支持网页字体加载，请填写系统字体名。');
      return;
    }
    const family = `CalendarCustomFont${Date.now()}`;
    const url = URL.createObjectURL(file);
    try {
      const fontFace = new FontFace(family, `url(${url})`);
      await fontFace.load();
      document.fonts.add(fontFace);
      customCalendarFontFamily = `"${family}", ${elements.font.value || 'sans-serif'}`;
      elements.font.value = file.name.replace(/\.(ttf|otf|woff2?)$/i, '');
      elements.fontPreset.value = 'custom';
      renderCalendarStylePreview();
      addLog('自定义日历字体已加载。');
    } catch (error) {
      addLog(`字体加载失败：${error.message || error}`);
    } finally {
      URL.revokeObjectURL(url);
    }
  });
  Object.values(elements.sizes).forEach((input) => input && updateCalendarFontOutput(input));
  elements.reset?.addEventListener('click', resetCalendarFontSizes);
  elements.render?.addEventListener('click', () => applyCalendarStyleToImageCanvas());
  elements.send?.addEventListener('click', () => applyCalendarStyleToImageCanvas({ forSend: true }));
  document.getElementById('weekStart')?.addEventListener('change', scheduleCalendarStylePreview);
}

function clampUiOpacity(value) {
  const opacity = parseFloat(value);
  if (Number.isNaN(opacity)) return DEFAULT_UI_OPACITY;
  return Math.min(1, Math.max(0, opacity));
}

function applyUiOpacity(value) {
  const opacity = clampUiOpacity(value);
  document.documentElement.style.setProperty('--ui-opacity', opacity.toFixed(2));
  document.documentElement.style.setProperty('--ui-footer-opacity', Math.max(0, opacity - 0.1).toFixed(2));
  document.documentElement.style.setProperty('--ui-border-opacity', opacity.toFixed(2));
  document.documentElement.style.setProperty('--ui-border-soft-opacity', (opacity * 0.08).toFixed(3));
  document.documentElement.style.setProperty('--ui-blue-border-soft-opacity', (opacity * 0.16).toFixed(3));

  const range = document.getElementById('uiOpacityRange');
  const label = document.getElementById('uiOpacityValue');
  if (range) {
    range.value = opacity.toFixed(2);
    updateRangeFill(range);
  }
  if (label) label.innerText = `${Math.round(opacity * 100)}%`;
}

function loadUiOpacity() {
  try {
    applyUiOpacity(localStorage.getItem(UI_OPACITY_STORAGE_KEY) || DEFAULT_UI_OPACITY);
  } catch (e) {
    console.error(e);
    applyUiOpacity(DEFAULT_UI_OPACITY);
  }
}

function saveUiOpacity(value) {
  const opacity = clampUiOpacity(value);
  applyUiOpacity(opacity);
  try {
    localStorage.setItem(UI_OPACITY_STORAGE_KEY, opacity.toFixed(2));
  } catch (e) {
    console.error(e);
  }
}

function clampGlassClarity(value) {
  const clarity = parseFloat(value);
  if (Number.isNaN(clarity)) return DEFAULT_GLASS_CLARITY;
  return Math.min(1, Math.max(0, clarity));
}

function applyGlassClarity(value) {
  const clarity = clampGlassClarity(value);
  const blur = (1 - clarity) * MAX_GLASS_BLUR;
  const backgroundBlur = blur * 0.55;
  document.documentElement.style.setProperty('--glass-blur-size', `${blur.toFixed(1)}px`);
  document.documentElement.style.setProperty('--page-bg-glass-blur-size', `${backgroundBlur.toFixed(1)}px`);

  const range = document.getElementById('glassClarityRange');
  const label = document.getElementById('glassClarityValue');
  if (range) {
    range.value = clarity.toFixed(2);
    updateRangeFill(range);
  }
  if (label) label.innerText = `${Math.round(clarity * 100)}%`;
}

function loadGlassClarity() {
  try {
    applyGlassClarity(localStorage.getItem(GLASS_CLARITY_STORAGE_KEY) || DEFAULT_GLASS_CLARITY);
  } catch (e) {
    console.error(e);
    applyGlassClarity(DEFAULT_GLASS_CLARITY);
  }
}

function saveGlassClarity(value) {
  const clarity = clampGlassClarity(value);
  applyGlassClarity(clarity);
  try {
    localStorage.setItem(GLASS_CLARITY_STORAGE_KEY, clarity.toFixed(2));
  } catch (e) {
    console.error(e);
  }
}

function clampNumber(value, min, max, fallback) {
  const number = parseFloat(value);
  if (Number.isNaN(number)) return fallback;
  return Math.min(max, Math.max(min, number));
}

function normalizePageBackgroundSettings(settings) {
  const source = settings && typeof settings === 'object' ? settings : {};
  const fit = ['cover', 'contain', '100% 100%'].includes(source.fit) ? source.fit : DEFAULT_PAGE_BACKGROUND_SETTINGS.fit;
  return {
    fit,
    zoom: clampNumber(source.zoom, 0.5, 3, DEFAULT_PAGE_BACKGROUND_SETTINGS.zoom),
    offsetX: clampNumber(source.offsetX, -40, 40, DEFAULT_PAGE_BACKGROUND_SETTINGS.offsetX),
    offsetY: clampNumber(source.offsetY, -40, 40, DEFAULT_PAGE_BACKGROUND_SETTINGS.offsetY),
    rotate: clampNumber(source.rotate, -180, 180, DEFAULT_PAGE_BACKGROUND_SETTINGS.rotate),
    flipX: source.flipX === true,
    flipY: source.flipY === true,
    brightness: clampNumber(source.brightness, 0.4, 1.6, DEFAULT_PAGE_BACKGROUND_SETTINGS.brightness),
    contrast: clampNumber(source.contrast, 0.5, 1.8, DEFAULT_PAGE_BACKGROUND_SETTINGS.contrast),
    saturation: clampNumber(source.saturation, 0, 2, DEFAULT_PAGE_BACKGROUND_SETTINGS.saturation),
    mask: clampNumber(source.mask, 0, 0.7, DEFAULT_PAGE_BACKGROUND_SETTINGS.mask)
  };
}

function setRangeControl(rangeId, labelId, value, formatter) {
  const range = document.getElementById(rangeId);
  const label = document.getElementById(labelId);
  if (range) {
    range.value = value;
    updateRangeFill(range);
  }
  if (label) label.innerText = formatter(value);
}

function syncPageBackgroundSettingsControls(settings) {
  setRangeControl('bgZoomRange', 'bgZoomValue', settings.zoom, (value) => `${Math.round(value * 100)}%`);
  setRangeControl('bgOffsetXRange', 'bgOffsetXValue', settings.offsetX, (value) => `${Math.round(value)}%`);
  setRangeControl('bgOffsetYRange', 'bgOffsetYValue', settings.offsetY, (value) => `${Math.round(value)}%`);
  setRangeControl('bgRotateRange', 'bgRotateValue', settings.rotate, (value) => `${Math.round(value)}°`);
  setRangeControl('bgBrightnessRange', 'bgBrightnessValue', settings.brightness, (value) => `${Math.round(value * 100)}%`);
  setRangeControl('bgContrastRange', 'bgContrastValue', settings.contrast, (value) => `${Math.round(value * 100)}%`);
  setRangeControl('bgSaturationRange', 'bgSaturationValue', settings.saturation, (value) => `${Math.round(value * 100)}%`);
  setRangeControl('bgMaskRange', 'bgMaskValue', settings.mask, (value) => `${Math.round(value * 100)}%`);

  document.querySelectorAll('[data-bg-fit]').forEach((button) => {
    button.classList.toggle('active', button.dataset.bgFit === settings.fit);
  });
  document.querySelectorAll('[data-bg-toggle]').forEach((button) => {
    button.classList.toggle('active', settings[button.dataset.bgToggle] === true);
  });
}

function applyPageBackgroundSettings(settings) {
  const normalized = normalizePageBackgroundSettings(settings);
  document.documentElement.style.setProperty('--page-bg-fit', normalized.fit);
  document.documentElement.style.setProperty(
    '--page-bg-transform',
    `translate(${normalized.offsetX}%, ${normalized.offsetY}%) scale(${normalized.flipX ? -normalized.zoom : normalized.zoom}, ${normalized.flipY ? -normalized.zoom : normalized.zoom}) rotate(${normalized.rotate}deg)`
  );
  document.documentElement.style.setProperty(
    '--page-bg-filter',
    `brightness(${normalized.brightness}) contrast(${normalized.contrast}) saturate(${normalized.saturation})`
  );
  document.documentElement.style.setProperty('--page-bg-overlay-opacity', normalized.mask.toFixed(2));
  syncPageBackgroundSettingsControls(normalized);
  return normalized;
}

function savePageBackgroundSettings(settings) {
  const normalized = applyPageBackgroundSettings(settings);
  try {
    localStorage.setItem(PAGE_BACKGROUND_SETTINGS_STORAGE_KEY, JSON.stringify(normalized));
  } catch (e) {
    console.error(e);
  }
  return normalized;
}

function loadPageBackgroundSettings() {
  let settings = DEFAULT_PAGE_BACKGROUND_SETTINGS;
  try {
    const stored = localStorage.getItem(PAGE_BACKGROUND_SETTINGS_STORAGE_KEY);
    if (stored) settings = JSON.parse(stored);
  } catch (e) {
    console.error(e);
  }
  return applyPageBackgroundSettings(settings);
}

function updatePageBackgroundSetting(key, value) {
  const current = readPageBackgroundSettingsFromControls();
  current[key] = value;
  savePageBackgroundSettings(current);
}

function readPageBackgroundSettingsFromControls() {
  const activeFit = document.querySelector('[data-bg-fit].active');
  return normalizePageBackgroundSettings({
    fit: activeFit ? activeFit.dataset.bgFit : DEFAULT_PAGE_BACKGROUND_SETTINGS.fit,
    flipX: document.querySelector('[data-bg-toggle="flipX"]')?.classList.contains('active'),
    flipY: document.querySelector('[data-bg-toggle="flipY"]')?.classList.contains('active'),
    zoom: document.getElementById('bgZoomRange')?.value,
    offsetX: document.getElementById('bgOffsetXRange')?.value,
    offsetY: document.getElementById('bgOffsetYRange')?.value,
    rotate: document.getElementById('bgRotateRange')?.value,
    brightness: document.getElementById('bgBrightnessRange')?.value,
    contrast: document.getElementById('bgContrastRange')?.value,
    saturation: document.getElementById('bgSaturationRange')?.value,
    mask: document.getElementById('bgMaskRange')?.value
  });
}

function openBackgroundSettings() {
  const modal = document.getElementById('backgroundSettingsModal');
  if (modal) modal.hidden = false;
}

function closeBackgroundSettings() {
  const modal = document.getElementById('backgroundSettingsModal');
  if (modal) modal.hidden = true;
}

function toggleBackgroundControls(forceOpen) {
  const panel = document.getElementById('backgroundControls');
  const button = document.getElementById('toggleBackgroundControls');
  if (!panel || !button) return;
  const show = typeof forceOpen === 'boolean' ? forceOpen : panel.hidden;
  panel.hidden = !show;
  button.classList.toggle('active', show);
  button.setAttribute('aria-expanded', String(show));
}

function resetBackgroundAdjustments() {
  savePageBackgroundSettings(DEFAULT_PAGE_BACKGROUND_SETTINGS);
}

function applyPageBackground(dataUrl) {
  if (!dataUrl) {
    document.body.classList.remove('custom-background');
    document.documentElement.style.setProperty('--page-bg-image', 'none');
    return;
  }

  document.body.classList.add('custom-background');
  document.documentElement.style.setProperty('--page-bg-image', `url("${dataUrl}")`);
}

function loadPageBackground() {
  try {
    applyPageBackground(localStorage.getItem(PAGE_BACKGROUND_STORAGE_KEY));
  } catch (e) {
    console.error(e);
  }
}

function clearPageBackground() {
  try {
    localStorage.removeItem(PAGE_BACKGROUND_STORAGE_KEY);
  } catch (e) {
    console.error(e);
  }
  const input = document.getElementById('pageBackgroundFile');
  if (input) input.value = '';
  applyPageBackground('');
}

function resetBackgroundDefaults() {
  try {
    localStorage.removeItem(PAGE_BACKGROUND_STORAGE_KEY);
    localStorage.removeItem(PAGE_BACKGROUND_SETTINGS_STORAGE_KEY);
    localStorage.removeItem(UI_OPACITY_STORAGE_KEY);
    localStorage.removeItem(GLASS_CLARITY_STORAGE_KEY);
  } catch (e) {
    console.error(e);
  }
  const input = document.getElementById('pageBackgroundFile');
  if (input) input.value = '';
  applyPageBackground('');
  applyPageBackgroundSettings(DEFAULT_PAGE_BACKGROUND_SETTINGS);
  applyUiOpacity(DEFAULT_UI_OPACITY);
  applyGlassClarity(DEFAULT_GLASS_CLARITY);
}

function resizeBackgroundImage(image) {
  const scale = Math.min(1, PAGE_BACKGROUND_MAX_SIZE / Math.max(image.width, image.height));
  const width = Math.max(1, Math.round(image.width * scale));
  const height = Math.max(1, Math.round(image.height * scale));
  const bgCanvas = document.createElement('canvas');
  const bgCtx = bgCanvas.getContext('2d');
  bgCanvas.width = width;
  bgCanvas.height = height;
  bgCtx.fillStyle = '#ffffff';
  bgCtx.fillRect(0, 0, width, height);
  bgCtx.drawImage(image, 0, 0, width, height);
  return bgCanvas.toDataURL('image/jpeg', PAGE_BACKGROUND_QUALITY);
}

function setPageBackgroundFromFile(file) {
  if (!file) return;
  if (!file.type.startsWith('image/')) {
    alert('请选择图片文件作为网页背景。');
    return;
  }

  const image = new Image();
  image.onload = function () {
    URL.revokeObjectURL(image.src);
    try {
      const dataUrl = resizeBackgroundImage(image);
      localStorage.setItem(PAGE_BACKGROUND_STORAGE_KEY, dataUrl);
      savePageBackgroundSettings(DEFAULT_PAGE_BACKGROUND_SETTINGS);
      applyPageBackground(dataUrl);
    } catch (e) {
      console.error(e);
      alert('背景图片保存失败，请换一张更小的图片。');
    }
  };
  image.onerror = function () {
    URL.revokeObjectURL(image.src);
    alert('背景图片读取失败，请换一张图片。');
  };
  image.src = URL.createObjectURL(file);
}

function setActiveGlobalNav(link) {
  document.querySelectorAll('.global-nav a').forEach((item) => item.classList.remove('active'));
  if (link) link.classList.add('active');
}

function initGlobalNavActive() {
  const links = document.querySelectorAll('.global-nav a');
  links.forEach((link) => {
    link.addEventListener('click', () => setActiveGlobalNav(link));
  });

  const current = Array.from(links).find((link) => link.getAttribute('href') === window.location.hash);
  setActiveGlobalNav(current || document.querySelector('.global-nav .global-brand'));
}

function updateRangeFill(range) {
  if (!range) return;
  const min = parseFloat(range.min || '0');
  const max = parseFloat(range.max || '100');
  const value = parseFloat(range.value || '0');
  const percent = max === min ? 0 : ((value - min) / (max - min)) * 100;
  range.style.setProperty('--range-fill', `${Math.max(0, Math.min(100, percent))}%`);
}

function initRangeFill() {
  document.querySelectorAll('input[type="range"]').forEach((range) => {
    updateRangeFill(range);
    range.addEventListener('input', () => updateRangeFill(range));
  });
}

function initEventHandlers() {
  initGlobalNavActive();
  initRangeFill();
  initLedColorControl();
  initCalendarStyleControls();
  updateDriverMeta();
  document.getElementById("clear-canvas").addEventListener("click", clearCanvas);
  const imageDropZone = document.getElementById('imageDropZone');
  const imageFile = document.getElementById('imageFile');
  if (imageDropZone && imageFile) {
    imageDropZone.addEventListener('dragover', (event) => {
      event.preventDefault();
      imageDropZone.classList.add('drag-over');
    });
    imageDropZone.addEventListener('dragleave', () => imageDropZone.classList.remove('drag-over'));
    imageDropZone.addEventListener('drop', (event) => {
      event.preventDefault();
      imageDropZone.classList.remove('drag-over');
      const file = event.dataTransfer && event.dataTransfer.files ? event.dataTransfer.files[0] : null;
      if (!file || !file.type.startsWith('image/')) {
        addLog('拖放失败：请选择有效的图片文件。');
        return;
      }
      try {
        const transfer = new DataTransfer();
        transfer.items.add(file);
        imageFile.files = transfer.files;
      } catch (_) {
        addLog('浏览器无法同步拖放文件，请改用文件选择按钮。');
        return;
      }
      updateImage(file);
    });
  }
  document.getElementById("resetDitherAdjustments").addEventListener("click", resetDitherAdjustments);
  document.getElementById("pageBackgroundFile").addEventListener("change", (e) => {
    setPageBackgroundFromFile(e.target.files[0]);
  });
  document.getElementById("toggleBackgroundControls").addEventListener("click", () => toggleBackgroundControls());
  document.getElementById("openBackgroundSettings").addEventListener("click", openBackgroundSettings);
  document.getElementById("closeBackgroundSettings").addEventListener("click", closeBackgroundSettings);
  document.getElementById("doneBackgroundSettings").addEventListener("click", closeBackgroundSettings);
  document.getElementById("resetBackgroundAdjustments").addEventListener("click", resetBackgroundAdjustments);
  document.getElementById("backgroundSettingsModal").addEventListener("click", (e) => {
    if (e.target.id === 'backgroundSettingsModal') closeBackgroundSettings();
  });
  document.querySelectorAll('[data-bg-fit]').forEach((button) => {
    button.addEventListener('click', () => updatePageBackgroundSetting('fit', button.dataset.bgFit));
  });
  document.querySelectorAll('[data-bg-toggle]').forEach((button) => {
    button.addEventListener('click', () => {
      const current = readPageBackgroundSettingsFromControls();
      current[button.dataset.bgToggle] = !current[button.dataset.bgToggle];
      savePageBackgroundSettings(current);
    });
  });
  [
    ['bgZoomRange', 'zoom'],
    ['bgOffsetXRange', 'offsetX'],
    ['bgOffsetYRange', 'offsetY'],
    ['bgRotateRange', 'rotate'],
    ['bgBrightnessRange', 'brightness'],
    ['bgContrastRange', 'contrast'],
    ['bgSaturationRange', 'saturation'],
    ['bgMaskRange', 'mask']
  ].forEach(([rangeId, key]) => {
    document.getElementById(rangeId).addEventListener('input', (e) => updatePageBackgroundSetting(key, e.target.value));
  });
  document.getElementById("clearPageBackground").addEventListener("click", clearPageBackground);
  document.getElementById("resetBackgroundDefaults").addEventListener("click", resetBackgroundDefaults);
  document.getElementById("uiOpacityRange").addEventListener("input", (e) => {
    saveUiOpacity(e.target.value);
  });
  document.getElementById("glassClarityRange").addEventListener("input", (e) => {
    saveGlassClarity(e.target.value);
  });
  document.getElementById("ditherMode").addEventListener("change", () => {
    if (paintManager && typeof paintManager.refreshMatterTemplatePalette === 'function') {
      paintManager.refreshMatterTemplatePalette();
    }
  });
  document.getElementById("ditherStrength").addEventListener("input", (e) => {
    document.getElementById("ditherStrengthValue").innerText = parseFloat(e.target.value).toFixed(1);
    applyDither();
  });
  document.getElementById("ditherContrast").addEventListener("input", (e) => {
    document.getElementById("ditherContrastValue").innerText = parseFloat(e.target.value).toFixed(1);
    applyDither();
  });
  document.getElementById("ditherBrightness").addEventListener("input", (e) => {
    document.getElementById("ditherBrightnessValue").innerText = parseFloat(e.target.value).toFixed(1);
    applyDither();
  });
  document.getElementById("ditherSaturation").addEventListener("input", (e) => {
    document.getElementById("ditherSaturationValue").innerText = parseFloat(e.target.value).toFixed(1);
    applyDither();
  });
}

function checkDebugMode() {
  const link = document.getElementById('debug-toggle');
  const urlParams = new URLSearchParams(window.location.search);
  const debugMode = urlParams.get('debug');

  if (debugMode === 'true') {
    document.body.classList.add('dark-mode');
    link.innerHTML = '正常模式';
    link.setAttribute('href', window.location.pathname);
    addLog("注意：开发模式功能已开启！错误设置可能导致连接异常或显示异常，不懂请不要随意修改，否则后果自负！", "⚠", "warning");
  } else {
    document.body.classList.remove('dark-mode');
    link.innerHTML = '开发模式';
    link.setAttribute('href', window.location.pathname + '?debug=true');
  }
}

document.body.onload = () => {
  textDecoder = null;
  canvas = document.getElementById('canvas');
  ctx = canvas.getContext("2d");
  configureTgzUi();

  ctx.fillStyle = 'white';
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  paintManager = new PaintManager(canvas, ctx);
  cropManager = new CropManager(canvas, ctx, paintManager);
  cropManager.setRenderCallback(renderTransformedImagePreview);
  if (paintManager.setBaseImageData) paintManager.setBaseImageData();

  paintManager.initPaintTools();
  cropManager.initCropTools();
  initEventHandlers();
  window.addEventListener('pagehide', disconnectDeviceOnPageExit);
  window.addEventListener('beforeunload', disconnectDeviceOnPageExit);
  disconnectStaleBleConnections();
  updateButtonStatus();
  checkDebugMode();
  loadUiOpacity();
  loadGlassClarity();
  loadPageBackgroundSettings();
  loadPageBackground();
  addLog('TGZ-52811 离线上位机 v20260826.10；图片和滤镜均只在本机处理');
}




