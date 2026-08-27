(function (root, factory) {
  const api = factory();
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  root.MemobusClient = api;
})(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';

  const FRAME_SYNC = 0xa5;
  const FRAME_TAIL = 0x5a;
  const BLUFI_CUSTOM_DATA = 0x4d;
  const BLUFI_DIRECTION_DEVICE_TO_CLIENT = 0x04;
  const BLUFI_FRAGMENT = 0x10;
  const MAX_MEMOBUS_PAYLOAD = 8192;
  const IMAGE_HEADER_BYTES = 8;
  const MAX_IMAGE_PACKETS = 256;

  function crc32(bytes) {
    let crc = 0;
    for (const byte of bytes) {
      crc ^= byte;
      for (let bit = 0; bit < 8; bit++) {
        crc = ((crc >>> 1) ^ ((crc & 1) ? 0xedb88320 : 0)) >>> 0;
      }
    }
    return (crc ^ 0xffffffff) >>> 0;
  }

  function concatBytes(parts) {
    const length = parts.reduce((sum, part) => sum + part.length, 0);
    const output = new Uint8Array(length);
    let offset = 0;
    for (const part of parts) {
      output.set(part, offset);
      offset += part.length;
    }
    return output;
  }

  function encodeMemobusRequest(group, fn, format, body) {
    const requestBody = body == null ? new Uint8Array(0) : Uint8Array.from(body);
    const payloadLength = 5 + requestBody.length;
    if (payloadLength > MAX_MEMOBUS_PAYLOAD) throw new RangeError('Memobus payload exceeds 8192 bytes');

    const payload = new Uint8Array(payloadLength);
    payload[0] = group;
    payload[1] = fn;
    payload[2] = format;
    payload[3] = requestBody.length & 0xff;
    payload[4] = requestBody.length >>> 8;
    payload.set(requestBody, 5);

    const checksum = crc32(payload);
    const frame = new Uint8Array(payloadLength + 9);
    frame[0] = FRAME_SYNC;
    frame[1] = 0;
    frame[2] = payloadLength & 0xff;
    frame[3] = payloadLength >>> 8;
    frame.set(payload, 4);
    const crcOffset = 4 + payloadLength;
    frame[crcOffset] = checksum & 0xff;
    frame[crcOffset + 1] = checksum >>> 8;
    frame[crcOffset + 2] = checksum >>> 16;
    frame[crcOffset + 3] = checksum >>> 24;
    frame[crcOffset + 4] = FRAME_TAIL;
    return frame;
  }

  function decodeMemobusFrame(value, options) {
    const frame = Uint8Array.from(value);
    if (frame.length < 14 || frame[0] !== FRAME_SYNC || frame.at(-1) !== FRAME_TAIL) {
      throw new Error('Invalid Memobus frame');
    }
    const payloadLength = frame[2] | frame[3] << 8;
    if (frame.length !== payloadLength + 9) throw new Error('Memobus frame length mismatch');
    const payload = frame.slice(4, 4 + payloadLength);
    const crcOffset = 4 + payloadLength;
    const receivedCrc = (frame[crcOffset] |
      frame[crcOffset + 1] << 8 |
      frame[crcOffset + 2] << 16 |
      frame[crcOffset + 3] << 24) >>> 0;
    if (crc32(payload) !== receivedCrc) throw new Error('Memobus CRC mismatch');

    const request = Boolean(options && options.request);
    const headerLength = request ? 5 : 6;
    if (payload.length < headerLength) throw new Error('Memobus payload too short');
    const bodyLengthOffset = request ? 3 : 4;
    const bodyLength = payload[bodyLengthOffset] | payload[bodyLengthOffset + 1] << 8;
    if (headerLength + bodyLength !== payload.length) throw new Error('Memobus body length mismatch');

    const decoded = {
      group: payload[0],
      function: payload[1],
      status: request ? undefined : payload[2],
      format: request ? payload[2] : payload[3],
      body: payload.slice(headerLength),
    };
    if (request) delete decoded.status;
    return decoded;
  }

  function decodeTlvs(value) {
    const data = Uint8Array.from(value);
    const fields = Object.create(null);
    let offset = 0;

    while (offset < data.length) {
      if (offset + 2 > data.length) throw new Error('TLV header is truncated');
      const type = data[offset++];
      const length = data[offset++];
      if (offset + length > data.length) throw new Error('TLV value is truncated');
      fields[type] = data.slice(offset, offset + length);
      offset += length;
    }
    return fields;
  }

  function fragmentBlufi(value, maxPacketLength, sequenceStart, deviceToClient) {
    const data = Uint8Array.from(value);
    const maxLength = Number(maxPacketLength);
    if (!Number.isInteger(maxLength) || maxLength < 7 || maxLength > 259) {
      throw new RangeError('BLUFI packet length must be between 7 and 259');
    }
    if (data.length === 0) throw new RangeError('BLUFI payload cannot be empty');

    const packets = [];
    const packetCapacity = Math.min(255, maxLength - 4);
    const fragmentCapacity = packetCapacity - 2;
    const direction = deviceToClient ? BLUFI_DIRECTION_DEVICE_TO_CLIENT : 0;
    let offset = 0;
    let sequence = Number(sequenceStart || 0) & 0xff;

    while (data.length - offset > packetCapacity) {
      const remaining = data.length - offset;
      const chunkLength = Math.min(fragmentCapacity, remaining);
      const packet = new Uint8Array(chunkLength + 6);
      packet[0] = BLUFI_CUSTOM_DATA;
      packet[1] = direction | BLUFI_FRAGMENT;
      packet[2] = sequence;
      packet[3] = chunkLength + 2;
      packet[4] = remaining & 0xff;
      packet[5] = remaining >>> 8;
      packet.set(data.slice(offset, offset + chunkLength), 6);
      packets.push(packet);
      offset += chunkLength;
      sequence = (sequence + 1) & 0xff;
    }

    const remaining = data.length - offset;
    const packet = new Uint8Array(remaining + 4);
    packet[0] = BLUFI_CUSTOM_DATA;
    packet[1] = direction;
    packet[2] = sequence;
    packet[3] = remaining;
    packet.set(data.slice(offset), 4);
    packets.push(packet);
    return packets;
  }

  class BlufiReassembler {
    constructor() {
      this.reset();
    }

    reset() {
      this.parts = [];
      this.remaining = 0;
      this.nextSequence = null;
    }

    push(value) {
      const packet = Uint8Array.from(value);
      if (packet.length < 4 || packet[0] !== BLUFI_CUSTOM_DATA || packet.length !== packet[3] + 4) {
        this.reset();
        throw new Error('Invalid BLUFI packet');
      }
      if (this.nextSequence != null && packet[2] !== this.nextSequence) {
        this.reset();
        throw new Error('BLUFI sequence mismatch');
      }
      this.nextSequence = (packet[2] + 1) & 0xff;

      const fragmented = (packet[1] & BLUFI_FRAGMENT) !== 0;
      if (fragmented) {
        if (packet[3] < 2) {
          this.reset();
          throw new Error('BLUFI fragment is too short');
        }
        const declaredRemaining = packet[4] | packet[5] << 8;
        const fragment = packet.slice(6);
        if ((this.remaining && declaredRemaining !== this.remaining) || fragment.length >= declaredRemaining) {
          this.reset();
          throw new Error('BLUFI fragment length mismatch');
        }
        this.parts.push(fragment);
        this.remaining = declaredRemaining - fragment.length;
        return null;
      }

      const finalPart = packet.slice(4);
      if (this.remaining && finalPart.length !== this.remaining) {
        this.reset();
        throw new Error('BLUFI final fragment length mismatch');
      }
      this.parts.push(finalPart);
      const completed = concatBytes(this.parts);
      this.reset();
      return completed;
    }
  }

  function rleEncode(data, maxLiteral = 128) {
    const input = data instanceof Uint8Array ? data : new Uint8Array(data);
    const output = [];
    let offset = 0;

    while (offset < input.length) {
      let runLength = 1;
      while (offset + runLength < input.length && runLength < 130 &&
             input[offset + runLength] === input[offset]) {
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
             !(offset + 2 < input.length && input[offset] === input[offset + 1] &&
               input[offset] === input[offset + 2])) {
        offset++;
        literalLength++;
      }
      if (literalLength === 0) {
        literalLength = 1;
        offset++;
      }
      output.push(literalLength - 1);
      for (let index = literalStart; index < literalStart + literalLength; index++) {
        output.push(input[index]);
      }
    }

    return new Uint8Array(output);
  }

  function rleDecode(data) {
    const input = data instanceof Uint8Array ? data : new Uint8Array(data);
    const output = [];
    let offset = 0;

    while (offset < input.length) {
      const token = input[offset++];
      if ((token & 0x80) !== 0) {
        if (offset >= input.length) throw new Error('RLE repeat token is incomplete');
        const count = (token & 0x7f) + 3;
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

  function imageTransferBytes(pixelBytes, width, height) {
    const pixels = Uint8Array.from(pixelBytes);
    const expectedPixels = width * height / 2;
    if (!Number.isInteger(expectedPixels) || pixels.length !== expectedPixels) {
      throw new RangeError(`Expected ${expectedPixels} packed pixels, received ${pixels.length}`);
    }
    return concatBytes([Uint8Array.from([
      0, 0, 0, 0,
      width >>> 8, width & 0xff,
      height >>> 8, height & 0xff,
    ]), pixels]);
  }

  function encodeImageChunks(chunks, packetBase, format) {
    const total = chunks.length;
    if (total === 0 || total > MAX_IMAGE_PACKETS) {
      throw new RangeError('Image requires more than 256 Memobus packets');
    }
    return chunks.map((chunk, packet) => {
      const body = new Uint8Array(4 + chunk.length);
      body[0] = total & 0xff;
      body[1] = total >>> 8;
      const packetIndex = packet + packetBase;
      body[2] = packetIndex & 0xff;
      body[3] = packetIndex >>> 8;
      body.set(chunk, 4);
      return encodeMemobusRequest(0x02, 0x01, format, body);
    });
  }

  function createImageRequests(pixelBytes, options) {
    const settings = options || {};
    const width = Number(settings.width || 760);
    const height = Number(settings.height || 528);
    const chunkSize = Number(settings.chunkSize || 8000);
    const packetBase = settings.packetBase == null ? 0 : Number(settings.packetBase);
    const format = Number(settings.format || 0) & 0xff;
    if (!Number.isInteger(chunkSize) || chunkSize < 1 || chunkSize > MAX_MEMOBUS_PAYLOAD - 9) {
      throw new RangeError('Image chunk size must be between 1 and 8183');
    }
    if (!Number.isInteger(packetBase) || packetBase < 0 || packetBase > 0xffff - MAX_IMAGE_PACKETS) {
      throw new RangeError('Image packet base is invalid');
    }

    const transfer = imageTransferBytes(pixelBytes, width, height);
    const total = Math.ceil(transfer.length / chunkSize);
    const chunks = [];
    for (let packet = 0; packet < total; packet++) {
      chunks.push(transfer.slice(packet * chunkSize, (packet + 1) * chunkSize));
    }
    return encodeImageChunks(chunks, packetBase, format);
  }

  function createOptimizedImageTransfer(pixelBytes, options) {
    const settings = options || {};
    const width = Number(settings.width || 760);
    const height = Number(settings.height || 528);
    const chunkSize = Number(settings.chunkSize || 1024);
    const packetBase = settings.packetBase == null ? 0 : Number(settings.packetBase);
    if (!Number.isInteger(chunkSize) || chunkSize < 1 ||
        chunkSize > MAX_MEMOBUS_PAYLOAD - 9) {
      throw new RangeError('Image chunk size must be between 1 and 8183');
    }
    if (!Number.isInteger(packetBase) || packetBase < 0 ||
        packetBase > 0xffff - MAX_IMAGE_PACKETS) {
      throw new RangeError('Image packet base is invalid');
    }

    const transfer = imageTransferBytes(pixelBytes, width, height);
    const rawChunks = [];
    const rleChunks = [];
    let compressedBytes = 0;
    for (let offset = 0; offset < transfer.length; offset += chunkSize) {
      const rawChunk = transfer.slice(offset, offset + chunkSize);
      const rleChunk = rleEncode(rawChunk);
      rawChunks.push(rawChunk);
      rleChunks.push(rleChunk);
      compressedBytes += rleChunk.length;
    }
    const compressed = compressedBytes < transfer.length;
    const chunks = compressed ? rleChunks : rawChunks;
    return {
      requests: encodeImageChunks(chunks, packetBase, compressed ? 0x04 : 0x00),
      compressed,
      sourceBytes: transfer.length,
      transferBytes: compressed ? compressedBytes : transfer.length,
    };
  }

  function packOfficialPalettePixels(imageData, inkMode, options) {
    if (!imageData || !imageData.data || !Number.isInteger(imageData.width) ||
        !Number.isInteger(imageData.height)) {
      throw new TypeError('Valid ImageData-compatible input is required');
    }
    const pixelCount = imageData.width * imageData.height;
    if ((pixelCount & 1) !== 0 || imageData.data.length !== pixelCount * 4) {
      throw new RangeError('Image dimensions or RGBA data length are invalid');
    }
    const palette = [
      [0, 0, 0],
      [255, 255, 255],
      [255, 255, 0],
      [255, 0, 0],
      [0, 255, 0],
      [0, 0, 255],
    ];
    const transferCodes = [0, 1, 2, 3, 6, 5];
    const paletteLength = inkMode === 'fourColor' ? 4 : 6;
    const mirrorHorizontal = Boolean(options && options.mirrorHorizontal);
    const output = new Uint8Array(pixelCount / 2);
    for (let pixel = 0; pixel < pixelCount; pixel++) {
      const row = Math.floor(pixel / imageData.width);
      const column = pixel % imageData.width;
      const sourceColumn = mirrorHorizontal ? imageData.width - 1 - column : column;
      const offset = (row * imageData.width + sourceColumn) * 4;
      const red = imageData.data[offset];
      const green = imageData.data[offset + 1];
      const blue = imageData.data[offset + 2];
      let selected = 0;
      let shortest = Infinity;
      for (let index = 0; index < paletteLength; index++) {
        const color = palette[index];
        const dr = red - color[0];
        const dg = green - color[1];
        const db = blue - color[2];
        const distance = dr * dr + dg * dg + db * db;
        if (distance < shortest) {
          shortest = distance;
          selected = index;
        }
      }
      const transferCode = transferCodes[selected];
      if ((pixel & 1) === 0) output[pixel >> 1] = transferCode << 4;
      else output[pixel >> 1] |= transferCode;
    }
    return output;
  }

  return {
    BlufiReassembler,
    concatBytes,
    createOptimizedImageTransfer,
    createImageRequests,
    crc32,
    decodeMemobusFrame,
    decodeTlvs,
    encodeMemobusRequest,
    fragmentBlufi,
    packOfficialPalettePixels,
    rleDecode,
    rleEncode,
  };
});
